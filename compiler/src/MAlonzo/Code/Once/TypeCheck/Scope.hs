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
import qualified MAlonzo.Code.Once.Spec.Surface.Generators
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
-- Once.TypeCheck.Scope.Head
d_Head_262 = ()
data T_Head_262
  = C_hv'45'gen_264 MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 |
    C_hv'45'gen'8321'_266 MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8
                          MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_8 |
    C_hv'45'gen'8322'_268 MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8
                          MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_8
                          MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_8 |
    C_hv'45'lam_270 | C_hv'45'other_272
-- Once.TypeCheck.Scope.headView
d_headView_274 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_8 -> T_Head_262
d_headView_274 v0
  = let v1 = coe C_hv'45'other_272 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RGen_16 v2
           -> coe C_hv'45'gen_264 (coe v2)
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_18 v2 v3
           -> case coe v2 of
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_RGen_16 v4
                  -> coe C_hv'45'gen'8321'_266 (coe v4) (coe v3)
                MAlonzo.Code.Once.Spec.Surface.Syntax.C_RApp_18 v4 v5
                  -> case coe v4 of
                       MAlonzo.Code.Once.Spec.Surface.Syntax.C_RGen_16 v6
                         -> coe C_hv'45'gen'8322'_268 (coe v6) (coe v5) (coe v3)
                       _ -> coe v1
                _ -> coe v1
         MAlonzo.Code.Once.Spec.Surface.Syntax.C_RLam_20 v2 v3
           -> coe C_hv'45'lam_270
         _ -> coe v1)
-- Once.TypeCheck.Scope.GenKindView
d_GenKindView_294 a0 = ()
data T_GenKindView_294
  = C_gk'45'map_298 MAlonzo.Code.Once.Spec.Surface.Generators.T_IsMap_76 |
    C_gk'45'const_300 | C_gk'45'comb'8321'_302 | C_gk'45'comb'8322'_304
-- Once.TypeCheck.Scope.genKindView
d_genKindView_308 ::
  MAlonzo.Code.Once.Spec.Surface.Generators.T_Gen_8 ->
  T_GenKindView_294
d_genKindView_308 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Surface.Generators.C_id_10
        -> coe
             C_gk'45'map_298
             (coe MAlonzo.Code.Once.Spec.Surface.Generators.C_is'45'map_80)
      MAlonzo.Code.Once.Spec.Surface.Generators.C_compose_12
        -> coe C_gk'45'comb'8322'_304
      MAlonzo.Code.Once.Spec.Surface.Generators.C_fst_14
        -> coe
             C_gk'45'map_298
             (coe MAlonzo.Code.Once.Spec.Surface.Generators.C_is'45'map_80)
      MAlonzo.Code.Once.Spec.Surface.Generators.C_snd_16
        -> coe
             C_gk'45'map_298
             (coe MAlonzo.Code.Once.Spec.Surface.Generators.C_is'45'map_80)
      MAlonzo.Code.Once.Spec.Surface.Generators.C_terminal_18
        -> coe
             C_gk'45'map_298
             (coe MAlonzo.Code.Once.Spec.Surface.Generators.C_is'45'map_80)
      MAlonzo.Code.Once.Spec.Surface.Generators.C_pair_20
        -> coe C_gk'45'comb'8322'_304
      MAlonzo.Code.Once.Spec.Surface.Generators.C_inl_22
        -> coe
             C_gk'45'map_298
             (coe MAlonzo.Code.Once.Spec.Surface.Generators.C_is'45'map_80)
      MAlonzo.Code.Once.Spec.Surface.Generators.C_inr_24
        -> coe
             C_gk'45'map_298
             (coe MAlonzo.Code.Once.Spec.Surface.Generators.C_is'45'map_80)
      MAlonzo.Code.Once.Spec.Surface.Generators.C_initial_26
        -> coe
             C_gk'45'map_298
             (coe MAlonzo.Code.Once.Spec.Surface.Generators.C_is'45'map_80)
      MAlonzo.Code.Once.Spec.Surface.Generators.C_case_28
        -> coe C_gk'45'comb'8322'_304
      MAlonzo.Code.Once.Spec.Surface.Generators.C_apply_30
        -> coe
             C_gk'45'map_298
             (coe MAlonzo.Code.Once.Spec.Surface.Generators.C_is'45'map_80)
      MAlonzo.Code.Once.Spec.Surface.Generators.C_curry_32
        -> coe C_gk'45'comb'8321'_302
      MAlonzo.Code.Once.Spec.Surface.Generators.C_In_34
        -> coe
             C_gk'45'map_298
             (coe MAlonzo.Code.Once.Spec.Surface.Generators.C_is'45'map_80)
      MAlonzo.Code.Once.Spec.Surface.Generators.C_cata_36
        -> coe C_gk'45'comb'8321'_302
      MAlonzo.Code.Once.Spec.Surface.Generators.C_Out_38
        -> coe
             C_gk'45'map_298
             (coe MAlonzo.Code.Once.Spec.Surface.Generators.C_is'45'map_80)
      MAlonzo.Code.Once.Spec.Surface.Generators.C_ana_40
        -> coe C_gk'45'comb'8321'_302
      MAlonzo.Code.Once.Spec.Surface.Generators.C_unit_42
        -> coe C_gk'45'const_300
      MAlonzo.Code.Once.Spec.Surface.Generators.C_toFloat_44
        -> coe C_gk'45'const_300
      _ -> MAlonzo.RTE.mazUnreachableError
