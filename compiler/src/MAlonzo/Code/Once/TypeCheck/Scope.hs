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

module MAlonzo.Code.Once.TypeCheck.Scope where

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
import qualified MAlonzo.Code.Once.Context
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.TypeCheck.Scope.Binding
d_Binding_8 a0 = ()
data T_Binding_8
  = C_mkBinding_24 MAlonzo.Code.Agda.Builtin.String.T_String_6
                   MAlonzo.Code.Once.Spec.Type.T_Ty_8
                   MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
-- Once.TypeCheck.Scope.Binding.name
d_name_18 ::
  T_Binding_8 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_name_18 v0
  = case coe v0 of
      C_mkBinding_24 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Scope.Binding.type
d_type_20 :: T_Binding_8 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_type_20 v0
  = case coe v0 of
      C_mkBinding_24 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Scope.Binding.quantity
d_quantity_22 ::
  T_Binding_8 -> MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
d_quantity_22 v0
  = case coe v0 of
      C_mkBinding_24 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Scope.Ctx
d_Ctx_26 :: Integer -> ()
d_Ctx_26 = erased
-- Once.TypeCheck.Scope.extendCtx
d_extendCtx_32 ::
  Integer ->
  [T_Binding_8] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> [T_Binding_8]
d_extendCtx_32 ~v0 v1 v2 v3 = du_extendCtx_32 v1 v2 v3
du_extendCtx_32 ::
  [T_Binding_8] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> [T_Binding_8]
du_extendCtx_32 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe
         C_mkBinding_24 (coe v1) (coe v2)
         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12))
      (coe v0)
-- Once.TypeCheck.Scope.Imports
d_Imports_40 :: ()
d_Imports_40 = erased
-- Once.TypeCheck.Scope.PolyCtx
d_PolyCtx_42 :: ()
d_PolyCtx_42 = erased
-- Once.TypeCheck.Scope.lookupImport
d_lookupImport_44 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_lookupImport_44 v0 v1
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
                              else coe seq (coe v8) (coe d_lookupImport_44 (coe v3) (coe v1))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Scope.lookupPolyPrefix
d_lookupPolyPrefix_74 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupPolyPrefix_74 v0 v1
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
                                            (coe d_lookupPolyPrefix_74 (coe v3) (coe v1))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Scope.NamedCtx
d_NamedCtx_112 a0 = ()
data T_NamedCtx_112
  = C_mkCtx_144 Integer [T_Binding_8]
                MAlonzo.Code.Once.Spec.Context.T_Ctx_8
                [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
                 MAlonzo.Code.Once.Spec.Type.T_Kind_70)
-- Once.TypeCheck.Scope.NamedCtx.size
d_size_130 :: T_NamedCtx_112 -> Integer
d_size_130 v0
  = case coe v0 of
      C_mkCtx_144 v1 v2 v3 v4 v5 v6 v7 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Scope.NamedCtx.named
d_named_132 :: T_NamedCtx_112 -> [T_Binding_8]
d_named_132 v0
  = case coe v0 of
      C_mkCtx_144 v1 v2 v3 v4 v5 v6 v7 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Scope.NamedCtx.debruijn
d_debruijn_134 ::
  T_NamedCtx_112 -> MAlonzo.Code.Once.Spec.Context.T_Ctx_8
d_debruijn_134 v0
  = case coe v0 of
      C_mkCtx_144 v1 v2 v3 v4 v5 v6 v7 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Scope.NamedCtx.imports
d_imports_136 ::
  T_NamedCtx_112 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_imports_136 v0
  = case coe v0 of
      C_mkCtx_144 v1 v2 v3 v4 v5 v6 v7 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Scope.NamedCtx.polys
d_polys_138 ::
  T_NamedCtx_112 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_polys_138 v0
  = case coe v0 of
      C_mkCtx_144 v1 v2 v3 v4 v5 v6 v7 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Scope.NamedCtx.sig
d_sig_140 ::
  T_NamedCtx_112 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_sig_140 v0
  = case coe v0 of
      C_mkCtx_144 v1 v2 v3 v4 v5 v6 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Scope.NamedCtx.kinds
d_kinds_142 ::
  T_NamedCtx_112 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Type.T_Kind_70
d_kinds_142 v0
  = case coe v0 of
      C_mkCtx_144 v1 v2 v3 v4 v5 v6 v7 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Scope.extendNamedCtx
d_extendNamedCtx_148 ::
  Integer ->
  T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_NamedCtx_112
d_extendNamedCtx_148 ~v0 v1 v2 v3 = du_extendNamedCtx_148 v1 v2 v3
du_extendNamedCtx_148 ::
  T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_NamedCtx_112
du_extendNamedCtx_148 v0 v1 v2
  = coe
      C_mkCtx_144
      (coe addInt (coe (1 :: Integer)) (coe d_size_130 (coe v0)))
      (coe du_extendCtx_32 (coe d_named_132 (coe v0)) (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Once.Spec.Context.C__'9656'__16
         (d_debruijn_134 (coe v0)) v2)
      (coe d_imports_136 (coe v0)) (coe d_polys_138 (coe v0))
      (coe d_sig_140 (coe v0)) (coe d_kinds_142 (coe v0))
-- Once.TypeCheck.Scope.lookupLocal-go
d_lookupLocal'45'go_170 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [T_Binding_8] ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupLocal'45'go_170 v0 v1 v2 v3 v4
  = case coe v3 of
      []
        -> coe
             seq (coe v4) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      (:) v5 v6
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Context.C_'8709'_12
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v8 v9
               -> let v10 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe
                    (coe
                       du_lookupLocal'45'at_214 (coe v0) (coe v10) (coe v2) (coe v6)
                       (coe v8) (coe v9)
                       (coe
                          MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v2)
                          (coe d_name_18 (coe v5))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Scope.lookupLocal-next
d_lookupLocal'45'next_188 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupLocal'45'next_188 ~v0 v1 v2 v3 v4
  = du_lookupLocal'45'next_188 v1 v2 v3 v4
du_lookupLocal'45'next_188 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_lookupLocal'45'next_188 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> case coe v8 of
                           MAlonzo.Code.Once.Context.C_svar_46 v11
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe
                                        MAlonzo.Code.Once.Spec.Context.du_lookup_22
                                        (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v1 v2)
                                        (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v11))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Spec.Context.d_singleUse_50
                                           (coe addInt (coe (1 :: Integer)) (coe v0))
                                           (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v11)
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_One_10))
                                        (coe
                                           MAlonzo.Code.Once.Context.C_svar_46
                                           (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v11))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Scope.lookupLocal-at
d_lookupLocal'45'at_214 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_Binding_8 ->
  [T_Binding_8] ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupLocal'45'at_214 v0 v1 v2 ~v3 v4 v5 v6 v7
  = du_lookupLocal'45'at_214 v0 v1 v2 v4 v5 v6 v7
du_lookupLocal'45'at_214 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [T_Binding_8] ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_lookupLocal'45'at_214 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
        -> if coe v7
             then coe
                    seq (coe v8)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Spec.Context.du_lookup_22
                             (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v4 v5)
                             (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe
                                MAlonzo.Code.Once.Spec.Context.d_singleUse_50
                                (coe addInt (coe (1 :: Integer)) (coe v1))
                                (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                                (coe MAlonzo.Code.Once.Spec.Grade.C_One_10))
                             (coe
                                MAlonzo.Code.Once.Context.C_svar_46
                                (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
             else coe
                    seq (coe v8)
                    (coe
                       du_lookupLocal'45'next_188 (coe v1) (coe v4) (coe v5)
                       (coe
                          d_lookupLocal'45'go_170 (coe v0) (coe v1) (coe v2) (coe v3)
                          (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Scope.lookupLocal
d_lookupLocal_256 ::
  Integer ->
  T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupLocal_256 v0 v1 v2
  = coe
      d_lookupLocal'45'go_170 (coe v0) (coe d_size_130 (coe v1)) (coe v2)
      (coe d_named_132 (coe v1)) (coe d_debruijn_134 (coe v1))
-- Once.TypeCheck.Scope._≟ₛ_
d__'8799''8347'__262 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799''8347'__262 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
      erased (coe (\ v2 -> v2))
      (coe
         MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
         (coe v1))
-- Once.TypeCheck.Scope.PolyBuiltinApp
d_PolyBuiltinApp_270 = ()
data T_PolyBuiltinApp_270
  = C_pba'45'id_272 | C_pba'45'fst_274 | C_pba'45'snd_276 |
    C_pba'45'terminal_278 | C_pba'45'inl_280 | C_pba'45'inr_282 |
    C_pba'45'initial_284 | C_pba'45'pair'45'applied_286 |
    C_pba'45'compose'45'applied_288 | C_pba'45'case'45'applied_290 |
    C_pba'45'curry_292 | C_pba'45'apply_294 | C_pba'45'In_296 |
    C_pba'45'cata_298 | C_pba'45'ana_300 | C_pba'45'Out_302
-- Once.TypeCheck.Scope.AppHeadView
d_AppHeadView_304 a0 = ()
data T_AppHeadView_304
  = C_ahv'45'id_306 | C_ahv'45'fst_308 | C_ahv'45'snd_310 |
    C_ahv'45'terminal_312 | C_ahv'45'inl_314 | C_ahv'45'inr_316 |
    C_ahv'45'initial_318 | C_ahv'45'curry_320 | C_ahv'45'apply_322 |
    C_ahv'45'In_324 | C_ahv'45'cata_326 | C_ahv'45'ana_328 |
    C_ahv'45'Out_330 | C_ahv'45'pair'45'applied_334 |
    C_ahv'45'compose'45'applied_338 | C_ahv'45'case'45'applied_342 |
    C_ahv'45'other_346
-- Once.TypeCheck.Scope.classifyAppHeadView
d_classifyAppHeadView_350 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  T_AppHeadView_304
d_classifyAppHeadView_350 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_70 v1
        -> coe C_ahv'45'other_346
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RQualified_72 v1 v2
        -> coe C_ahv'45'other_346
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74 v1
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Name.C_canonical_12 v2
               -> case coe v2 of
                    [] -> coe C_ahv'45'other_346
                    (:) v3 v4
                      -> case coe v4 of
                           [] -> coe C_ahv'45'other_346
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
                                                                              (coe C_ahv'45'id_306)
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
                                                                                                     C_ahv'45'fst_308)
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
                                                                                                                         C_ahv'45'snd_310)
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
                                                                                                                                             C_ahv'45'terminal_312)
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
                                                                                                                                                                 C_ahv'45'inl_314)
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
                                                                                                                                                                                     C_ahv'45'inr_316)
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
                                                                                                                                                                                                         C_ahv'45'initial_318)
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
                                                                                                                                                                                                                             C_ahv'45'curry_320)
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
                                                                                                                                                                                                                                                 C_ahv'45'apply_322)
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
                                                                                                                                                                                                                                                                     C_ahv'45'In_324)
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
                                                                                                                                                                                                                                                                                         C_ahv'45'cata_326)
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
                                                                                                                                                                                                                                                                                                             C_ahv'45'ana_328)
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
                                                                                                                                                                                                                                                                                                                                 C_ahv'45'Out_330)
                                                                                                                                                                                                                                                                                                                       else coe
                                                                                                                                                                                                                                                                                                                              seq
                                                                                                                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                                                                                                                 v48)
                                                                                                                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                                                                                                                 C_ahv'45'other_346)
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
                                                   else coe seq (coe v9) (coe C_ahv'45'other_346)
                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                  (:) v7 v8 -> coe C_ahv'45'other_346
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RVar_70 v3
               -> coe C_ahv'45'other_346
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RQualified_72 v3 v4
               -> coe C_ahv'45'other_346
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RResolved_74 v3
               -> case coe v3 of
                    MAlonzo.Code.Once.Spec.Name.C_canonical_12 v4
                      -> case coe v4 of
                           [] -> coe C_ahv'45'other_346
                           (:) v5 v6
                             -> case coe v6 of
                                  [] -> coe C_ahv'45'other_346
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
                                                                                        C_ahv'45'pair'45'applied_334)
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
                                                                                                            C_ahv'45'compose'45'applied_338)
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
                                                                                                                                C_ahv'45'case'45'applied_342)
                                                                                                                      else coe
                                                                                                                             seq
                                                                                                                             (coe
                                                                                                                                v20)
                                                                                                                             (coe
                                                                                                                                C_ahv'45'other_346)
                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                           _ -> MAlonzo.RTE.mazUnreachableError))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                          else coe
                                                                 seq (coe v11)
                                                                 (coe C_ahv'45'other_346)
                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                         (:) v9 v10 -> coe C_ahv'45'other_346
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_76 v3 v4
               -> coe C_ahv'45'other_346
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_78 v3 v4
               -> coe C_ahv'45'other_346
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLet_80 v3 v4 v5
               -> coe C_ahv'45'other_346
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RPair_82 v3 v4
               -> coe C_ahv'45'other_346
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RDestruct_84 v3 v4 v5 v6 v7
               -> coe C_ahv'45'other_346
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RUnit_86
               -> coe C_ahv'45'other_346
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RInt_88 v3
               -> coe C_ahv'45'other_346
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RFloat_90 v3 v4 v5
               -> coe C_ahv'45'other_346
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RAnnot_92 v3 v4
               -> coe C_ahv'45'other_346
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_94 v3 v4 v5
               -> coe C_ahv'45'other_346
             MAlonzo.Code.Once.Spec.Surface.Syntax.C_RNeg_96 v3
               -> coe C_ahv'45'other_346
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_78 v1 v2
        -> coe C_ahv'45'other_346
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLet_80 v1 v2 v3
        -> coe C_ahv'45'other_346
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RPair_82 v1 v2
        -> coe C_ahv'45'other_346
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RDestruct_84 v1 v2 v3 v4 v5
        -> coe C_ahv'45'other_346
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RUnit_86
        -> coe C_ahv'45'other_346
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RInt_88 v1
        -> coe C_ahv'45'other_346
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RFloat_90 v1 v2 v3
        -> coe C_ahv'45'other_346
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RAnnot_92 v1 v2
        -> coe C_ahv'45'other_346
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RBinOp_94 v1 v2 v3
        -> coe C_ahv'45'other_346
      MAlonzo.Code.Once.Spec.Surface.Syntax.C_RNeg_96 v1
        -> coe C_ahv'45'other_346
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Scope.viewToPba
d_viewToPba_578 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  T_AppHeadView_304 -> Maybe T_PolyBuiltinApp_270
d_viewToPba_578 ~v0 v1 = du_viewToPba_578 v1
du_viewToPba_578 :: T_AppHeadView_304 -> Maybe T_PolyBuiltinApp_270
du_viewToPba_578 v0
  = case coe v0 of
      C_ahv'45'id_306
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'id_272)
      C_ahv'45'fst_308
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'fst_274)
      C_ahv'45'snd_310
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'snd_276)
      C_ahv'45'terminal_312
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_pba'45'terminal_278)
      C_ahv'45'inl_314
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'inl_280)
      C_ahv'45'inr_316
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'inr_282)
      C_ahv'45'initial_318
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_pba'45'initial_284)
      C_ahv'45'curry_320
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'curry_292)
      C_ahv'45'apply_322
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'apply_294)
      C_ahv'45'In_324
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'In_296)
      C_ahv'45'cata_326
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'cata_298)
      C_ahv'45'ana_328
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'ana_300)
      C_ahv'45'Out_330
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'Out_302)
      C_ahv'45'pair'45'applied_334
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_pba'45'pair'45'applied_286)
      C_ahv'45'compose'45'applied_338
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_pba'45'compose'45'applied_288)
      C_ahv'45'case'45'applied_342
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_pba'45'case'45'applied_290)
      C_ahv'45'other_346
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Scope.classifyAppHead
d_classifyAppHead_580 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  Maybe T_PolyBuiltinApp_270
d_classifyAppHead_580 v0
  = coe du_viewToPba_578 (coe d_classifyAppHeadView_350 (coe v0))
