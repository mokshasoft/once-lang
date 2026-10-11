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

module MAlonzo.Code.Once.Spec.Typing.Scope where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Syntax
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Spec.Type.Grade
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Spec.Typing.Scope.Binding
d_Binding_8 = ()
data T_Binding_8
  = C_mkBinding_22 MAlonzo.Code.Agda.Builtin.String.T_String_6
                   MAlonzo.Code.Once.Spec.Type.T_Type_8
                   MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8
-- Once.Spec.Typing.Scope.Binding.name
d_name_16 ::
  T_Binding_8 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_name_16 v0
  = case coe v0 of
      C_mkBinding_22 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Typing.Scope.Binding.type
d_type_18 :: T_Binding_8 -> MAlonzo.Code.Once.Spec.Type.T_Type_8
d_type_18 v0
  = case coe v0 of
      C_mkBinding_22 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Typing.Scope.Binding.quantity
d_quantity_20 ::
  T_Binding_8 -> MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8
d_quantity_20 v0
  = case coe v0 of
      C_mkBinding_22 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Typing.Scope.Ctx
d_Ctx_24 :: ()
d_Ctx_24 = erased
-- Once.Spec.Typing.Scope.extendCtx
d_extendCtx_26 ::
  [T_Binding_8] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 -> [T_Binding_8]
d_extendCtx_26 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         C_mkBinding_22 (coe v1) (coe v2)
         (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14))
      (coe v0)
-- Once.Spec.Typing.Scope.Imports
d_Imports_34 :: ()
d_Imports_34 = erased
-- Once.Spec.Typing.Scope.PolyCtx
d_PolyCtx_36 :: ()
d_PolyCtx_36 = erased
-- Once.Spec.Typing.Scope.lookupImport
d_lookupImport_38 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Type_8
d_lookupImport_38 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> let v6
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v6 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe v4))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v4)
                               (coe v1)) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                         -> if coe v7
                              then coe
                                     seq (coe v8)
                                     (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5))
                              else coe seq (coe v8) (coe d_lookupImport_38 (coe v3) (coe v1))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Typing.Scope.lookupPolyPrefix
d_lookupPolyPrefix_68 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupPolyPrefix_68 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> let v8
                               = coe
                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                   erased
                                   (\ v8 ->
                                      coe
                                        MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                        (coe v4))
                                   (coe
                                      MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v4)
                                      (coe v1)) in
                         coe
                           (case coe v8 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                -> if coe v9
                                     then coe
                                            seq (coe v10)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v6)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v7) (coe v3))))
                                     else coe
                                            seq (coe v10)
                                            (coe d_lookupPolyPrefix_68 (coe v3) (coe v1))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Typing.Scope.NamedCtx
d_NamedCtx_104 = ()
data T_NamedCtx_104
  = C_mkCtx_130 Integer [T_Binding_8]
                MAlonzo.Code.Once.Spec.Context.T_Ctx_6
                [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
-- Once.Spec.Typing.Scope.NamedCtx.size
d_size_118 :: T_NamedCtx_104 -> Integer
d_size_118 v0
  = case coe v0 of
      C_mkCtx_130 v1 v2 v3 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Typing.Scope.NamedCtx.named
d_named_120 :: T_NamedCtx_104 -> [T_Binding_8]
d_named_120 v0
  = case coe v0 of
      C_mkCtx_130 v1 v2 v3 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Typing.Scope.NamedCtx.debruijn
d_debruijn_122 ::
  T_NamedCtx_104 -> MAlonzo.Code.Once.Spec.Context.T_Ctx_6
d_debruijn_122 v0
  = case coe v0 of
      C_mkCtx_130 v1 v2 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Typing.Scope.NamedCtx.imports
d_imports_124 ::
  T_NamedCtx_104 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_imports_124 v0
  = case coe v0 of
      C_mkCtx_130 v1 v2 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Typing.Scope.NamedCtx.polys
d_polys_126 ::
  T_NamedCtx_104 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_polys_126 v0
  = case coe v0 of
      C_mkCtx_130 v1 v2 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Typing.Scope.NamedCtx.sig
d_sig_128 ::
  T_NamedCtx_104 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_sig_128 v0
  = case coe v0 of
      C_mkCtx_130 v1 v2 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Typing.Scope.extendNamedCtx
d_extendNamedCtx_132 ::
  T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 -> T_NamedCtx_104
d_extendNamedCtx_132 v0 v1 v2
  = case coe v0 of
      C_mkCtx_130 v3 v4 v5 v6 v7 v8
        -> coe
             C_mkCtx_130 (coe addInt (coe (1 :: Integer)) (coe v3))
             (coe d_extendCtx_26 (coe v4) (coe v1) (coe v2))
             (coe
                MAlonzo.Code.Once.Spec.Context.C__'44'_'94'__12 v5 v2
                (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14))
             (coe v6) (coe v7) (coe v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Typing.Scope.lookupLocal-go
d_lookupLocal'45'go_162 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [T_Binding_8] ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupLocal'45'go_162 v0 v1 v2 v3
  = case coe v2 of
      []
        -> coe
             seq (coe v3) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      (:) v4 v5
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Context.C_'8709'_8
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Spec.Context.C__'44'_'94'__12 v7 v8 v9
               -> let v10 = subInt (coe v0) (coe (1 :: Integer)) in
                  coe
                    (let v11
                           = coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v11 ->
                                  coe
                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                    (coe v1))
                               (coe
                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v1)
                                  (coe d_name_16 (coe v4))) in
                     coe
                       (case coe v11 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                            -> if coe v12
                                 then coe
                                        seq (coe v13)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                              (coe
                                                 MAlonzo.Code.Once.Spec.Context.du_lookup_24
                                                 (coe
                                                    MAlonzo.Code.Once.Spec.Context.C__'44'_'94'__12
                                                    v7 v8 v9)
                                                 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe
                                                    MAlonzo.Code.Once.Spec.Context.d_singleUse_62
                                                    (coe v0)
                                                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                                                    (coe
                                                       MAlonzo.Code.Once.Spec.Type.Grade.C_One_12))
                                                 (coe
                                                    MAlonzo.Code.Once.Spec.Context.C_svar_120
                                                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
                                 else coe
                                        seq (coe v13)
                                        (let v14
                                               = d_lookupLocal'45'go_162
                                                   (coe v10) (coe v1) (coe v5) (coe v7) in
                                         coe
                                           (case coe v14 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                -> case coe v15 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                       -> case coe v17 of
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                              -> case coe v19 of
                                                                   MAlonzo.Code.Once.Spec.Context.C_svar_120 v22
                                                                     -> coe
                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe
                                                                                MAlonzo.Code.Once.Spec.Context.du_lookup_24
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Spec.Context.C__'44'_'94'__12
                                                                                   v7 v8 v9)
                                                                                (coe
                                                                                   MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                                   v22))
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Spec.Context.d_singleUse_62
                                                                                   (coe v0)
                                                                                   (coe
                                                                                      MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                                      v22)
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Spec.Type.Grade.C_One_12))
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Spec.Context.C_svar_120
                                                                                   (coe
                                                                                      MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                                      v22))))
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                -> coe v14
                                              _ -> MAlonzo.RTE.mazUnreachableError))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Typing.Scope.lookupLocal
d_lookupLocal_250 ::
  T_NamedCtx_104 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupLocal_250 v0 v1
  = coe
      d_lookupLocal'45'go_162 (coe d_size_118 (coe v0)) (coe v1)
      (coe d_named_120 (coe v0)) (coe d_debruijn_122 (coe v0))
-- Once.Spec.Typing.Scope._≟ₛ_
d__'8799''8347'__256 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799''8347'__256 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
      erased (coe (\ v2 -> v2))
      (coe
         MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
         (coe v1))
-- Once.Spec.Typing.Scope.PolyBuiltinApp
d_PolyBuiltinApp_264 = ()
data T_PolyBuiltinApp_264
  = C_pba'45'id_266 | C_pba'45'fst_268 | C_pba'45'snd_270 |
    C_pba'45'terminal_272 | C_pba'45'inl_274 | C_pba'45'inr_276 |
    C_pba'45'initial_278 | C_pba'45'pair'45'applied_280 |
    C_pba'45'compose'45'applied_282 | C_pba'45'case'45'applied_284 |
    C_pba'45'curry_286 | C_pba'45'apply_288 | C_pba'45'In_290 |
    C_pba'45'cata_292 | C_pba'45'ana_294 | C_pba'45'Out_296
-- Once.Spec.Typing.Scope.AppHeadView
d_AppHeadView_298 a0 = ()
data T_AppHeadView_298
  = C_ahv'45'id_300 | C_ahv'45'fst_302 | C_ahv'45'snd_304 |
    C_ahv'45'terminal_306 | C_ahv'45'inl_308 | C_ahv'45'inr_310 |
    C_ahv'45'initial_312 | C_ahv'45'curry_314 | C_ahv'45'apply_316 |
    C_ahv'45'In_318 | C_ahv'45'cata_320 | C_ahv'45'ana_322 |
    C_ahv'45'Out_324 | C_ahv'45'pair'45'applied_328 |
    C_ahv'45'compose'45'applied_332 | C_ahv'45'case'45'applied_336 |
    C_ahv'45'other_340
-- Once.Spec.Typing.Scope.classifyAppHeadView
d_classifyAppHeadView_344 ::
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 -> T_AppHeadView_298
d_classifyAppHeadView_344 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Syntax.C_RVar_36 v1
        -> coe C_ahv'45'other_340
      MAlonzo.Code.Once.Spec.Syntax.C_RQualified_38 v1 v2
        -> coe C_ahv'45'other_340
      MAlonzo.Code.Once.Spec.Syntax.C_RResolved_40 v1
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Name.C_canonical_12 v2
               -> case coe v2 of
                    [] -> coe C_ahv'45'other_340
                    (:) v3 v4
                      -> case coe v4 of
                           [] -> coe C_ahv'45'other_340
                           (:) v5 v6
                             -> case coe v6 of
                                  []
                                    -> let v7
                                             = coe
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                 erased (coe (\ v7 -> v7))
                                                 (coe
                                                    MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                                    (coe v3)
                                                    (coe
                                                       MAlonzo.Code.Once.Spec.Name.d_generatorNS_18)) in
                                       coe
                                         (case coe v7 of
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                              -> if coe v8
                                                   then coe
                                                          seq (coe v9)
                                                          (let v10
                                                                 = coe
                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                     erased (coe (\ v10 -> v10))
                                                                     (coe
                                                                        MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                                                        (coe v5)
                                                                        (coe
                                                                           ("id"
                                                                            ::
                                                                            Data.Text.Text))) in
                                                           coe
                                                             (case coe v10 of
                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                                                  -> if coe v11
                                                                       then coe
                                                                              seq (coe v12)
                                                                              (coe C_ahv'45'id_300)
                                                                       else coe
                                                                              seq (coe v12)
                                                                              (let v13
                                                                                     = coe
                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                         erased
                                                                                         (coe
                                                                                            (\ v13 ->
                                                                                               v13))
                                                                                         (coe
                                                                                            MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                                                                            (coe v5)
                                                                                            (coe
                                                                                               ("fst"
                                                                                                ::
                                                                                                Data.Text.Text))) in
                                                                               coe
                                                                                 (case coe v13 of
                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                                                      -> if coe v14
                                                                                           then coe
                                                                                                  seq
                                                                                                  (coe
                                                                                                     v15)
                                                                                                  (coe
                                                                                                     C_ahv'45'fst_302)
                                                                                           else coe
                                                                                                  seq
                                                                                                  (coe
                                                                                                     v15)
                                                                                                  (let v16
                                                                                                         = coe
                                                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                             erased
                                                                                                             (coe
                                                                                                                (\ v16 ->
                                                                                                                   v16))
                                                                                                             (coe
                                                                                                                MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                                                                                                (coe
                                                                                                                   v5)
                                                                                                                (coe
                                                                                                                   ("snd"
                                                                                                                    ::
                                                                                                                    Data.Text.Text))) in
                                                                                                   coe
                                                                                                     (case coe
                                                                                                             v16 of
                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                                                          -> if coe
                                                                                                                  v17
                                                                                                               then coe
                                                                                                                      seq
                                                                                                                      (coe
                                                                                                                         v18)
                                                                                                                      (coe
                                                                                                                         C_ahv'45'snd_304)
                                                                                                               else coe
                                                                                                                      seq
                                                                                                                      (coe
                                                                                                                         v18)
                                                                                                                      (let v19
                                                                                                                             = coe
                                                                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                 erased
                                                                                                                                 (coe
                                                                                                                                    (\ v19 ->
                                                                                                                                       v19))
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                                                                                                                    (coe
                                                                                                                                       v5)
                                                                                                                                    (coe
                                                                                                                                       ("terminal"
                                                                                                                                        ::
                                                                                                                                        Data.Text.Text))) in
                                                                                                                       coe
                                                                                                                         (case coe
                                                                                                                                 v19 of
                                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                                                                              -> if coe
                                                                                                                                      v20
                                                                                                                                   then coe
                                                                                                                                          seq
                                                                                                                                          (coe
                                                                                                                                             v21)
                                                                                                                                          (coe
                                                                                                                                             C_ahv'45'terminal_306)
                                                                                                                                   else coe
                                                                                                                                          seq
                                                                                                                                          (coe
                                                                                                                                             v21)
                                                                                                                                          (let v22
                                                                                                                                                 = coe
                                                                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                     erased
                                                                                                                                                     (coe
                                                                                                                                                        (\ v22 ->
                                                                                                                                                           v22))
                                                                                                                                                     (coe
                                                                                                                                                        MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                                                                                                                                        (coe
                                                                                                                                                           v5)
                                                                                                                                                        (coe
                                                                                                                                                           ("inl"
                                                                                                                                                            ::
                                                                                                                                                            Data.Text.Text))) in
                                                                                                                                           coe
                                                                                                                                             (case coe
                                                                                                                                                     v22 of
                                                                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                                                                                                                                  -> if coe
                                                                                                                                                          v23
                                                                                                                                                       then coe
                                                                                                                                                              seq
                                                                                                                                                              (coe
                                                                                                                                                                 v24)
                                                                                                                                                              (coe
                                                                                                                                                                 C_ahv'45'inl_308)
                                                                                                                                                       else coe
                                                                                                                                                              seq
                                                                                                                                                              (coe
                                                                                                                                                                 v24)
                                                                                                                                                              (let v25
                                                                                                                                                                     = coe
                                                                                                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                         erased
                                                                                                                                                                         (coe
                                                                                                                                                                            (\ v25 ->
                                                                                                                                                                               v25))
                                                                                                                                                                         (coe
                                                                                                                                                                            MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                                                                                                                                                            (coe
                                                                                                                                                                               v5)
                                                                                                                                                                            (coe
                                                                                                                                                                               ("inr"
                                                                                                                                                                                ::
                                                                                                                                                                                Data.Text.Text))) in
                                                                                                                                                               coe
                                                                                                                                                                 (case coe
                                                                                                                                                                         v25 of
                                                                                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v26 v27
                                                                                                                                                                      -> if coe
                                                                                                                                                                              v26
                                                                                                                                                                           then coe
                                                                                                                                                                                  seq
                                                                                                                                                                                  (coe
                                                                                                                                                                                     v27)
                                                                                                                                                                                  (coe
                                                                                                                                                                                     C_ahv'45'inr_310)
                                                                                                                                                                           else coe
                                                                                                                                                                                  seq
                                                                                                                                                                                  (coe
                                                                                                                                                                                     v27)
                                                                                                                                                                                  (let v28
                                                                                                                                                                                         = coe
                                                                                                                                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                             erased
                                                                                                                                                                                             (coe
                                                                                                                                                                                                (\ v28 ->
                                                                                                                                                                                                   v28))
                                                                                                                                                                                             (coe
                                                                                                                                                                                                MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                                                                                                                                                                                (coe
                                                                                                                                                                                                   v5)
                                                                                                                                                                                                (coe
                                                                                                                                                                                                   ("initial"
                                                                                                                                                                                                    ::
                                                                                                                                                                                                    Data.Text.Text))) in
                                                                                                                                                                                   coe
                                                                                                                                                                                     (case coe
                                                                                                                                                                                             v28 of
                                                                                                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v29 v30
                                                                                                                                                                                          -> if coe
                                                                                                                                                                                                  v29
                                                                                                                                                                                               then coe
                                                                                                                                                                                                      seq
                                                                                                                                                                                                      (coe
                                                                                                                                                                                                         v30)
                                                                                                                                                                                                      (coe
                                                                                                                                                                                                         C_ahv'45'initial_312)
                                                                                                                                                                                               else coe
                                                                                                                                                                                                      seq
                                                                                                                                                                                                      (coe
                                                                                                                                                                                                         v30)
                                                                                                                                                                                                      (let v31
                                                                                                                                                                                                             = coe
                                                                                                                                                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                                                 erased
                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                    (\ v31 ->
                                                                                                                                                                                                                       v31))
                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                    MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                       v5)
                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                       ("curry"
                                                                                                                                                                                                                        ::
                                                                                                                                                                                                                        Data.Text.Text))) in
                                                                                                                                                                                                       coe
                                                                                                                                                                                                         (case coe
                                                                                                                                                                                                                 v31 of
                                                                                                                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v32 v33
                                                                                                                                                                                                              -> if coe
                                                                                                                                                                                                                      v32
                                                                                                                                                                                                                   then coe
                                                                                                                                                                                                                          seq
                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                             v33)
                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                             C_ahv'45'curry_314)
                                                                                                                                                                                                                   else coe
                                                                                                                                                                                                                          seq
                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                             v33)
                                                                                                                                                                                                                          (let v34
                                                                                                                                                                                                                                 = coe
                                                                                                                                                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                                                                     erased
                                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                                        (\ v34 ->
                                                                                                                                                                                                                                           v34))
                                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                                        MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                                                                                                                                                                                                                        (coe
                                                                                                                                                                                                                                           v5)
                                                                                                                                                                                                                                        (coe
                                                                                                                                                                                                                                           ("apply"
                                                                                                                                                                                                                                            ::
                                                                                                                                                                                                                                            Data.Text.Text))) in
                                                                                                                                                                                                                           coe
                                                                                                                                                                                                                             (case coe
                                                                                                                                                                                                                                     v34 of
                                                                                                                                                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v35 v36
                                                                                                                                                                                                                                  -> if coe
                                                                                                                                                                                                                                          v35
                                                                                                                                                                                                                                       then coe
                                                                                                                                                                                                                                              seq
                                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                                 v36)
                                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                                 C_ahv'45'apply_316)
                                                                                                                                                                                                                                       else coe
                                                                                                                                                                                                                                              seq
                                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                                 v36)
                                                                                                                                                                                                                                              (let v37
                                                                                                                                                                                                                                                     = coe
                                                                                                                                                                                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                                                                                         erased
                                                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                                                            (\ v37 ->
                                                                                                                                                                                                                                                               v37))
                                                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                                                            MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                                                                                                                                                                                                                                            (coe
                                                                                                                                                                                                                                                               v5)
                                                                                                                                                                                                                                                            (coe
                                                                                                                                                                                                                                                               ("In"
                                                                                                                                                                                                                                                                ::
                                                                                                                                                                                                                                                                Data.Text.Text))) in
                                                                                                                                                                                                                                               coe
                                                                                                                                                                                                                                                 (case coe
                                                                                                                                                                                                                                                         v37 of
                                                                                                                                                                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v38 v39
                                                                                                                                                                                                                                                      -> if coe
                                                                                                                                                                                                                                                              v38
                                                                                                                                                                                                                                                           then coe
                                                                                                                                                                                                                                                                  seq
                                                                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                                                                     v39)
                                                                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                                                                     C_ahv'45'In_318)
                                                                                                                                                                                                                                                           else coe
                                                                                                                                                                                                                                                                  seq
                                                                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                                                                     v39)
                                                                                                                                                                                                                                                                  (let v40
                                                                                                                                                                                                                                                                         = coe
                                                                                                                                                                                                                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                                                                                                             erased
                                                                                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                                                                                (\ v40 ->
                                                                                                                                                                                                                                                                                   v40))
                                                                                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                                                                                MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                                                                                                                                                                                                                                                                (coe
                                                                                                                                                                                                                                                                                   v5)
                                                                                                                                                                                                                                                                                (coe
                                                                                                                                                                                                                                                                                   ("cata"
                                                                                                                                                                                                                                                                                    ::
                                                                                                                                                                                                                                                                                    Data.Text.Text))) in
                                                                                                                                                                                                                                                                   coe
                                                                                                                                                                                                                                                                     (case coe
                                                                                                                                                                                                                                                                             v40 of
                                                                                                                                                                                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v41 v42
                                                                                                                                                                                                                                                                          -> if coe
                                                                                                                                                                                                                                                                                  v41
                                                                                                                                                                                                                                                                               then coe
                                                                                                                                                                                                                                                                                      seq
                                                                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                                                                         v42)
                                                                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                                                                         C_ahv'45'cata_320)
                                                                                                                                                                                                                                                                               else coe
                                                                                                                                                                                                                                                                                      seq
                                                                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                                                                         v42)
                                                                                                                                                                                                                                                                                      (let v43
                                                                                                                                                                                                                                                                                             = coe
                                                                                                                                                                                                                                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                                                                                                                                 erased
                                                                                                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                                                                                                    (\ v43 ->
                                                                                                                                                                                                                                                                                                       v43))
                                                                                                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                                                                                                    MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                                                                                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                                                                                                       v5)
                                                                                                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                                                                                                       ("ana"
                                                                                                                                                                                                                                                                                                        ::
                                                                                                                                                                                                                                                                                                        Data.Text.Text))) in
                                                                                                                                                                                                                                                                                       coe
                                                                                                                                                                                                                                                                                         (case coe
                                                                                                                                                                                                                                                                                                 v43 of
                                                                                                                                                                                                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v44 v45
                                                                                                                                                                                                                                                                                              -> if coe
                                                                                                                                                                                                                                                                                                      v44
                                                                                                                                                                                                                                                                                                   then coe
                                                                                                                                                                                                                                                                                                          seq
                                                                                                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                                                                                                             v45)
                                                                                                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                                                                                                             C_ahv'45'ana_322)
                                                                                                                                                                                                                                                                                                   else coe
                                                                                                                                                                                                                                                                                                          seq
                                                                                                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                                                                                                             v45)
                                                                                                                                                                                                                                                                                                          (let v46
                                                                                                                                                                                                                                                                                                                 = coe
                                                                                                                                                                                                                                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                                                                                                                                                     erased
                                                                                                                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                                                                                                                        (\ v46 ->
                                                                                                                                                                                                                                                                                                                           v46))
                                                                                                                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                                                                                                                        MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                                                                                                                                                                                                                                                                                                        (coe
                                                                                                                                                                                                                                                                                                                           v5)
                                                                                                                                                                                                                                                                                                                        (coe
                                                                                                                                                                                                                                                                                                                           ("Out"
                                                                                                                                                                                                                                                                                                                            ::
                                                                                                                                                                                                                                                                                                                            Data.Text.Text))) in
                                                                                                                                                                                                                                                                                                           coe
                                                                                                                                                                                                                                                                                                             (case coe
                                                                                                                                                                                                                                                                                                                     v46 of
                                                                                                                                                                                                                                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v47 v48
                                                                                                                                                                                                                                                                                                                  -> if coe
                                                                                                                                                                                                                                                                                                                          v47
                                                                                                                                                                                                                                                                                                                       then coe
                                                                                                                                                                                                                                                                                                                              seq
                                                                                                                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                                                                                                                 v48)
                                                                                                                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                                                                                                                 C_ahv'45'Out_324)
                                                                                                                                                                                                                                                                                                                       else coe
                                                                                                                                                                                                                                                                                                                              seq
                                                                                                                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                                                                                                                 v48)
                                                                                                                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                                                                                                                 C_ahv'45'other_340)
                                                                                                                                                                                                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                                                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError))
                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                                   else coe seq (coe v9) (coe C_ahv'45'other_340)
                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                  (:) v7 v8 -> coe C_ahv'45'other_340
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Syntax.C_RApp_42 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Syntax.C_RVar_36 v3
               -> coe C_ahv'45'other_340
             MAlonzo.Code.Once.Spec.Syntax.C_RQualified_38 v3 v4
               -> coe C_ahv'45'other_340
             MAlonzo.Code.Once.Spec.Syntax.C_RResolved_40 v3
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Name.C_canonical_12 v4
                      -> case coe v4 of
                           [] -> coe C_ahv'45'other_340
                           (:) v5 v6
                             -> case coe v6 of
                                  [] -> coe C_ahv'45'other_340
                                  (:) v7 v8
                                    -> case coe v8 of
                                         []
                                           -> let v9
                                                    = coe
                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                        erased (coe (\ v9 -> v9))
                                                        (coe
                                                           MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                                           (coe v5)
                                                           (coe
                                                              MAlonzo.Code.Once.Spec.Name.d_generatorNS_18)) in
                                              coe
                                                (case coe v9 of
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                                     -> if coe v10
                                                          then coe
                                                                 seq (coe v11)
                                                                 (let v12
                                                                        = coe
                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                            erased
                                                                            (coe (\ v12 -> v12))
                                                                            (coe
                                                                               MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                                                               (coe v7)
                                                                               (coe
                                                                                  ("pair"
                                                                                   ::
                                                                                   Data.Text.Text))) in
                                                                  coe
                                                                    (case coe v12 of
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                                         -> if coe v13
                                                                              then coe
                                                                                     seq (coe v14)
                                                                                     (coe
                                                                                        C_ahv'45'pair'45'applied_328)
                                                                              else coe
                                                                                     seq (coe v14)
                                                                                     (let v15
                                                                                            = coe
                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                erased
                                                                                                (coe
                                                                                                   (\ v15 ->
                                                                                                      v15))
                                                                                                (coe
                                                                                                   MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                                                                                   (coe
                                                                                                      v7)
                                                                                                   (coe
                                                                                                      ("compose"
                                                                                                       ::
                                                                                                       Data.Text.Text))) in
                                                                                      coe
                                                                                        (case coe
                                                                                                v15 of
                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                                             -> if coe
                                                                                                     v16
                                                                                                  then coe
                                                                                                         seq
                                                                                                         (coe
                                                                                                            v17)
                                                                                                         (coe
                                                                                                            C_ahv'45'compose'45'applied_332)
                                                                                                  else coe
                                                                                                         seq
                                                                                                         (coe
                                                                                                            v17)
                                                                                                         (let v18
                                                                                                                = coe
                                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                    erased
                                                                                                                    (coe
                                                                                                                       (\ v18 ->
                                                                                                                          v18))
                                                                                                                    (coe
                                                                                                                       MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                                                                                                       (coe
                                                                                                                          v7)
                                                                                                                       (coe
                                                                                                                          ("case"
                                                                                                                           ::
                                                                                                                           Data.Text.Text))) in
                                                                                                          coe
                                                                                                            (case coe
                                                                                                                    v18 of
                                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v19 v20
                                                                                                                 -> if coe
                                                                                                                         v19
                                                                                                                      then coe
                                                                                                                             seq
                                                                                                                             (coe
                                                                                                                                v20)
                                                                                                                             (coe
                                                                                                                                C_ahv'45'case'45'applied_336)
                                                                                                                      else coe
                                                                                                                             seq
                                                                                                                             (coe
                                                                                                                                v20)
                                                                                                                             (coe
                                                                                                                                C_ahv'45'other_340)
                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                           _ -> MAlonzo.RTE.mazUnreachableError))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                          else coe
                                                                 seq (coe v11)
                                                                 (coe C_ahv'45'other_340)
                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                         (:) v9 v10 -> coe C_ahv'45'other_340
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Syntax.C_RApp_42 v3 v4
               -> coe C_ahv'45'other_340
             MAlonzo.Code.Once.Spec.Syntax.C_RLam_44 v3 v4
               -> coe C_ahv'45'other_340
             MAlonzo.Code.Once.Spec.Syntax.C_RLet_46 v3 v4 v5
               -> coe C_ahv'45'other_340
             MAlonzo.Code.Once.Spec.Syntax.C_RPair_48 v3 v4
               -> coe C_ahv'45'other_340
             MAlonzo.Code.Once.Spec.Syntax.C_RDestruct_50 v3 v4 v5 v6 v7
               -> coe C_ahv'45'other_340
             MAlonzo.Code.Once.Spec.Syntax.C_RUnit_52 -> coe C_ahv'45'other_340
             MAlonzo.Code.Once.Spec.Syntax.C_RInt_54 v3
               -> coe C_ahv'45'other_340
             MAlonzo.Code.Once.Spec.Syntax.C_RFloat_56 v3 v4 v5 v6
               -> coe C_ahv'45'other_340
             MAlonzo.Code.Once.Spec.Syntax.C_RStringLit_58 v3
               -> coe C_ahv'45'other_340
             MAlonzo.Code.Once.Spec.Syntax.C_RAnnot_60 v3 v4
               -> coe C_ahv'45'other_340
             MAlonzo.Code.Once.Spec.Syntax.C_RBinOp_62 v3 v4 v5
               -> coe C_ahv'45'other_340
             MAlonzo.Code.Once.Spec.Syntax.C_RUnaryOp_64 v4
               -> coe C_ahv'45'other_340
             MAlonzo.Code.Once.Spec.Syntax.C_RAna_66 v3 v4
               -> coe C_ahv'45'other_340
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Syntax.C_RLam_44 v1 v2
        -> coe C_ahv'45'other_340
      MAlonzo.Code.Once.Spec.Syntax.C_RLet_46 v1 v2 v3
        -> coe C_ahv'45'other_340
      MAlonzo.Code.Once.Spec.Syntax.C_RPair_48 v1 v2
        -> coe C_ahv'45'other_340
      MAlonzo.Code.Once.Spec.Syntax.C_RDestruct_50 v1 v2 v3 v4 v5
        -> coe C_ahv'45'other_340
      MAlonzo.Code.Once.Spec.Syntax.C_RUnit_52 -> coe C_ahv'45'other_340
      MAlonzo.Code.Once.Spec.Syntax.C_RInt_54 v1
        -> coe C_ahv'45'other_340
      MAlonzo.Code.Once.Spec.Syntax.C_RFloat_56 v1 v2 v3 v4
        -> coe C_ahv'45'other_340
      MAlonzo.Code.Once.Spec.Syntax.C_RStringLit_58 v1
        -> coe C_ahv'45'other_340
      MAlonzo.Code.Once.Spec.Syntax.C_RAnnot_60 v1 v2
        -> coe C_ahv'45'other_340
      MAlonzo.Code.Once.Spec.Syntax.C_RBinOp_62 v1 v2 v3
        -> coe C_ahv'45'other_340
      MAlonzo.Code.Once.Spec.Syntax.C_RUnaryOp_64 v2
        -> coe C_ahv'45'other_340
      MAlonzo.Code.Once.Spec.Syntax.C_RAna_66 v1 v2
        -> coe C_ahv'45'other_340
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Typing.Scope.viewToPba
d_viewToPba_572 ::
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  T_AppHeadView_298 -> Maybe T_PolyBuiltinApp_264
d_viewToPba_572 ~v0 v1 = du_viewToPba_572 v1
du_viewToPba_572 :: T_AppHeadView_298 -> Maybe T_PolyBuiltinApp_264
du_viewToPba_572 v0
  = case coe v0 of
      C_ahv'45'id_300
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'id_266)
      C_ahv'45'fst_302
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'fst_268)
      C_ahv'45'snd_304
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'snd_270)
      C_ahv'45'terminal_306
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_pba'45'terminal_272)
      C_ahv'45'inl_308
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'inl_274)
      C_ahv'45'inr_310
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'inr_276)
      C_ahv'45'initial_312
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_pba'45'initial_278)
      C_ahv'45'curry_314
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'curry_286)
      C_ahv'45'apply_316
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'apply_288)
      C_ahv'45'In_318
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'In_290)
      C_ahv'45'cata_320
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'cata_292)
      C_ahv'45'ana_322
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'ana_294)
      C_ahv'45'Out_324
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'Out_296)
      C_ahv'45'pair'45'applied_328
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_pba'45'pair'45'applied_280)
      C_ahv'45'compose'45'applied_332
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_pba'45'compose'45'applied_282)
      C_ahv'45'case'45'applied_336
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_pba'45'case'45'applied_284)
      C_ahv'45'other_340
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Typing.Scope.classifyAppHead
d_classifyAppHead_574 ::
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  Maybe T_PolyBuiltinApp_264
d_classifyAppHead_574 v0
  = coe du_viewToPba_572 (coe d_classifyAppHeadView_344 (coe v0))
