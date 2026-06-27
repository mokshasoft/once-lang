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

module MAlonzo.Code.Once.Adequacy.CanonPolyTransport where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Adequacy.CanonPreserveMutual
import qualified MAlonzo.Code.Once.Parser.Module.Resolve
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.CanonPolyTransport.canonPolysCtx
d_canonPolysCtx_6 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_canonPolysCtx_6 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                 (coe
                                    MAlonzo.Code.Once.Parser.Module.Resolve.d_canonExpr_272 (coe v0)
                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v7))))
                           (coe d_canonPolysCtx_6 (coe v0) (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonPolyTransport.canon-entry
d_canon'45'entry_20 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_canon'45'entry_20 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe
                MAlonzo.Code.Once.Parser.Module.Resolve.d_canonExpr_272 (coe v0)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonPolyTransport.lookupPoly-canon
d_lookupPoly'45'canon_34 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookupPoly'45'canon_34 = erased
-- Once.Adequacy.CanonPolyTransport.removePoly-canon
d_removePoly'45'canon_86 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_removePoly'45'canon_86 = erased
-- Once.Adequacy.CanonPolyTransport.lookupPoly-canon-just
d_lookupPoly'45'canon'45'just_144 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_244 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookupPoly'45'canon'45'just_144 = erased
-- Once.Adequacy.CanonPolyTransport.PInB
d_PInB_166 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> ()
d_PInB_166 = erased
-- Once.Adequacy.CanonPolyTransport.lookupPoly-removePoly-mono
d_lookupPoly'45'removePoly'45'mono_188 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupPoly'45'removePoly'45'mono_188 v0 v1 v2 v3 v4
  = case coe v2 of
      (:) v5 v6
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> coe
                    seq (coe v8)
                    (let v9
                           = coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v9 ->
                                  coe
                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                    (coe v7))
                               (coe
                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v7)
                                  (coe v0)) in
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
                                                   (\ v12 ->
                                                      coe
                                                        MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                        (coe v7))
                                                   (coe
                                                      MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                      (coe v7) (coe v1)) in
                                         coe
                                           (case coe v12 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                -> if coe v13
                                                     then coe
                                                            seq (coe v14)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe v8) erased)
                                                     else coe
                                                            seq (coe v14)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe v3) (coe v4))
                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                 else coe
                                        seq (coe v11)
                                        (let v12
                                               = coe
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                   erased
                                                   (\ v12 ->
                                                      coe
                                                        MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                        (coe v7))
                                                   (coe
                                                      MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                      (coe v7) (coe v1)) in
                                         coe
                                           (case coe v12 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                -> if coe v13
                                                     then coe
                                                            seq (coe v14)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe v8) erased)
                                                     else coe
                                                            seq (coe v14)
                                                            (coe
                                                               d_lookupPoly'45'removePoly'45'mono_188
                                                               (coe v0) (coe v1) (coe v6) (coe v3)
                                                               erased)
                                              _ -> MAlonzo.RTE.mazUnreachableError))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonPolyTransport.removePoly-PInB
d_removePoly'45'PInB_310 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_244 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_244 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_removePoly'45'PInB_310 = erased
-- Once.Adequacy.CanonPolyTransport.composeMid-polys-canon
d_composeMid'45'polys'45'canon_362
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Adequacy.CanonPolyTransport.composeMid-polys-canon"
-- Once.Adequacy.CanonPolyTransport.polys-transport-ᵍ
d_polys'45'transport'45''7501'_384 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14
d_polys'45'transport'45''7501'_384 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                   v8 v9 v10
  = du_polys'45'transport'45''7501'_384 v8 v9 v10
du_polys'45'transport'45''7501'_384 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14
du_polys'45'transport'45''7501'_384 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'int_302
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'int_302
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'terminal_306
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'terminal_306
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'pair_318 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'42'__126 v12 v13
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'pair_318
                           (coe
                              du_polys'45'transport'45''7501'_384 (coe v10) (coe v12) (coe v8))
                           (coe
                              du_polys'45'transport'45''7501'_384 (coe v11) (coe v13) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inl_328 v7
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v10 v11
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inl_328
                           (coe
                              du_polys'45'transport'45''7501'_384 (coe v9) (coe v10) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inr_338 v7
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v10 v11
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inr_338
                           (coe
                              du_polys'45'transport'45''7501'_384 (coe v9) (coe v11) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'In_348 v6 v8
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_132 v11
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'In_348 v6
                           (coe
                              du_polys'45'transport'45''7501'_384 (coe v10)
                              (coe
                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v11) (coe v1))
                              (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonPolyTransport.polys-transport-ᵢ
d_polys'45'transport'45''7522'_450 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_244 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_polys'45'transport'45''7522'_450 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 v9
                                   v10 v11 v12
  = du_polys'45'transport'45''7522'_450
      v0 v1 v2 v3 v4 v5 v6 v7 v9 v10 v11 v12
du_polys'45'transport'45''7522'_450 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_polys'45'transport'45''7522'_450 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                    v10 v11
  = case coe v11 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_30
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_30
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'str_36
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'str_36
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_40
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_40
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_44
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_44
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_56 v16
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_56 v16
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_66
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_66
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_74
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_74
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_82
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_82
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_92 v16
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_58 v17 v18
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_92
                    (coe
                       du_polys'45'transport'45''7580'_500 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v17) (coe v9)
                       (coe v10) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_108 v17 v18 v19 v20
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v21 v22
               -> case coe v9 of
                    MAlonzo.Code.Once.Type.C__'42'__126 v23 v24
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_108 v17 v18
                           (coe
                              du_polys'45'transport'45''7522'_450 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v21) (coe v23)
                              (coe v17) (coe v19))
                           (coe
                              du_polys'45'transport'45''7522'_450 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v22) (coe v24)
                              (coe v18) (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_116 v15
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_62 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_116
                    (coe
                       du_polys'45'transport'45''7522'_450 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v17)
                       (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_136 v16 v18 v19 v20 v21 v22
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v23 v24 v25
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_136 v16 v18 v19 v20
                    (coe
                       du_polys'45'transport'45''7522'_450 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v24) (coe v16)
                       (coe v19) (coe v21))
                    (coe
                       du_polys'45'transport'45''7522'_450 (coe v0)
                       (coe addInt (coe (1 :: Integer)) (coe v1))
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v2)
                          (coe v23) (coe v16))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v3) (coe v16))
                       (coe v4) (coe v5) (coe v6) (coe v7) (coe v25) (coe v9)
                       (coe MAlonzo.Code.Once.Surface.Syntax.C__'8759'__66 v18 v20)
                       (coe v22))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_166 v18 v19 v21 v22 v23 v24 v25 v26 v27 v28
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v29 v30 v31 v32 v33
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_166 v18 v19 v21
                    v22 v23 v24 v25
                    (coe
                       du_polys'45'transport'45''7522'_450 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v29)
                       (coe MAlonzo.Code.Once.Type.C__'43'__128 (coe v18) (coe v19))
                       (coe v23) (coe v26))
                    (coe
                       du_polys'45'transport'45''7522'_450 (coe v0)
                       (coe addInt (coe (1 :: Integer)) (coe v1))
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v2)
                          (coe v30) (coe v18))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v3) (coe v18))
                       (coe v4) (coe v5) (coe v6) (coe v7) (coe v31) (coe v9)
                       (coe MAlonzo.Code.Once.Surface.Syntax.C__'8759'__66 v21 v24)
                       (coe v27))
                    (coe
                       du_polys'45'transport'45''7522'_450 (coe v0)
                       (coe addInt (coe (1 :: Integer)) (coe v1))
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v2)
                          (coe v32) (coe v19))
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v3) (coe v19))
                       (coe v4) (coe v5) (coe v6) (coe v7) (coe v33) (coe v9)
                       (coe MAlonzo.Code.Once.Surface.Syntax.C__'8759'__66 v22 v25)
                       (coe v28))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_180 v16 v17 v19 v20
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_60 v21 v22 v23
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_180 v16
                    v17
                    (coe
                       du_polys'45'transport'45''7522'_450 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v22)
                       (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v16) (coe v19))
                    (coe
                       du_polys'45'transport'45''7522'_450 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v23)
                       (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v17) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_194 v16 v17 v19 v20
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_60 v21 v22 v23
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_194 v16
                    v17
                    (coe
                       du_polys'45'transport'45''7522'_450 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v22)
                       (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v16) (coe v19))
                    (coe
                       du_polys'45'transport'45''7522'_450 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v23)
                       (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v17) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_204 v15 v16
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_204 v15
                    (coe
                       du_polys'45'transport'45''7522'_450 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v18) (coe v9)
                       (coe v15) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_216 v15 v16 v17
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_216 v15 v16
                    (coe
                       du_polys'45'transport'45''7522'_450 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v19)
                       (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v9) (coe v15))
                       (coe v16) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_228 v14 v16 v17
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_228 v14 v16
                    (coe
                       du_polys'45'transport'45''7522'_450 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v19)
                       (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v14) (coe v9))
                       (coe v16) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_238 v14 v15 v16
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_238 v14
                    v15
                    (coe
                       du_polys'45'transport'45''7522'_450 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v18) (coe v14)
                       (coe v15) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arr'45'app'45'infer_250 v17
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> case coe v9 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v20 v21 v22
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arr'45'app'45'infer_250
                           (coe
                              du_polys'45'transport'45''7522'_450 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v19)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v20)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe MAlonzo.Code.Once.Type.C_pure_34))
                                 (coe v22))
                              (coe v10) (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_262 v14 v16 v17
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_262
                    v14 v16
                    (coe
                       du_polys'45'transport'45''7522'_450 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v19)
                       (coe
                          MAlonzo.Code.Once.Type.C__'42'__126
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v14)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe v9))
                          (coe v14))
                       (coe v16) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_280 v15 v17 v18 v19 v21 v22
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v23 v24
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_280 v15 v17 v18 v19
                    (coe
                       du_polys'45'transport'45''7522'_450 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v23)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v15)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v17)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v9))
                       (coe v18) (coe v21))
                    (coe
                       du_polys'45'transport'45''7580'_500 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v24) (coe v15)
                       (coe v19) (coe v22))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_296 v15 v17 v18 v20 v21
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v22 v23
               -> case coe v9 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v24 v25 v26
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_296 v15 v17 v18
                           (coe
                              du_polys'45'transport'45''7522'_450 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v22)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v15)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe MAlonzo.Code.Once.Type.C_eff_36))
                                 (coe v26))
                              (coe v17) (coe v20))
                           (coe
                              du_polys'45'transport'45''7580'_500 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v23) (coe v15)
                              (coe v18) (coe v21))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonPolyTransport.polys-transport-ᵐ
d_polys'45'transport'45''7504'_476 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_244 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18
d_polys'45'transport'45''7504'_476 v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 ~v8
                                   v9 v10 v11 v12 v13
  = du_polys'45'transport'45''7504'_476 v0 v5 v7 v9 v10 v11 v12 v13
du_polys'45'transport'45''7504'_476 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18
du_polys'45'transport'45''7504'_476 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'id_356
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'id_356
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'fst_366
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'fst_366
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'snd_376
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'snd_376
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'terminal_384
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'terminal_384
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'initial_392
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'initial_392
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inl_402
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inl_402
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inr_412
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inr_412
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'compose_428 v12 v16 v17
        -> case coe v3 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v20 v21
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'compose_428 v12
                           (coe
                              du_polys'45'transport'45''7504'_476 (coe v0) (coe v1) (coe v2)
                              (coe v21) (coe v12) (coe v5) (coe v6) (coe v16))
                           (coe
                              du_polys'45'transport'45''7504'_476 (coe v0) (coe v1) (coe v2)
                              (coe v19) (coe v4) (coe v5) (coe v12) (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'case_444 v15 v16
        -> case coe v3 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v19 v20
                      -> case coe v4 of
                           MAlonzo.Code.Once.Type.C__'43'__128 v21 v22
                             -> coe
                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'case_444
                                  (coe
                                     du_polys'45'transport'45''7504'_476 (coe v0) (coe v1) (coe v2)
                                     (coe v20) (coe v21) (coe v5) (coe v6) (coe v15))
                                  (coe
                                     du_polys'45'transport'45''7504'_476 (coe v0) (coe v1) (coe v2)
                                     (coe v18) (coe v22) (coe v5) (coe v6) (coe v16))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'pair_458 v14 v15
        -> case coe v3 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
                      -> case coe v6 of
                           MAlonzo.Code.Once.Type.C__'42'__126 v20 v21
                             -> coe
                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'pair_458
                                  (coe
                                     du_polys'45'transport'45''7504'_476 (coe v0) (coe v1) (coe v2)
                                     (coe v19) (coe v4) (coe MAlonzo.Code.Once.Type.C_pure_34)
                                     (coe v20) (coe v14))
                                  (coe
                                     du_polys'45'transport'45''7504'_476 (coe v0) (coe v1) (coe v2)
                                     (coe v17) (coe v4) (coe MAlonzo.Code.Once.Type.C_pure_34)
                                     (coe v21) (coe v15))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'curry_470 v13
        -> case coe v3 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> case coe v6 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v16 v17 v18
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'curry_470
                           (coe
                              du_polys'45'transport'45''7504'_476 (coe v0) (coe v1) (coe v2)
                              (coe v15)
                              (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v4) (coe v16))
                              (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v18) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'cata_484 v13 v15
        -> case coe v3 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> case coe v4 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_132 v18
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'cata_484 v13
                           (coe
                              du_polys'45'transport'45''7580'_500 (coe v0) (coe (0 :: Integer))
                              (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                              (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
                              (coe (0 :: Integer)) (coe v1)
                              (coe MAlonzo.Code.Once.TypeCheck.Classify.d_emptySigEffects_12)
                              (coe v2) (coe v17)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                 (coe
                                    MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v18)
                                    (coe v6))
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v5))
                                 (coe v6))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_70
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_size_186
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_208
                                       (coe v1) (coe d_canonPolysCtx_6 (coe v0) (coe v2)))))
                              (coe v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'arr_494 v12
        -> case coe v3 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'arr_494
                    (coe
                       du_polys'45'transport'45''7504'_476 (coe v0) (coe v1) (coe v2)
                       (coe v14) (coe v4) (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v6)
                       (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_504 v12
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_504
             (coe
                du_polys'45'transport'45''7501'_384 (coe v3) (coe v6) (coe v12))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named_516
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named_516
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named'45'resolved_528
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named'45'resolved_528
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonPolyTransport.polys-transport-ᶜ
d_polys'45'transport'45''7580'_500 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_244 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
d_polys'45'transport'45''7580'_500 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 v9
                                   v10 v11 v12
  = du_polys'45'transport'45''7580'_500
      v0 v1 v2 v3 v4 v5 v6 v7 v9 v10 v11 v12
du_polys'45'transport'45''7580'_500 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
du_polys'45'transport'45''7580'_500 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                    v10 v11
  = case coe v11 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_540 v17
        -> case coe v9 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v18 v19 v20
               -> case coe v19 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v21 v22
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_540
                           (coe
                              du_polys'45'transport'45''7504'_476 (coe v0) (coe v5) (coe v7)
                              (coe v8) (coe v18) (coe v22) (coe v20) (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_550 v16
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_550
             (coe
                du_polys'45'transport'45''7522'_450 (coe v0) (coe v1) (coe v2)
                (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
                (coe v10) (coe v16))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_568 v18 v21
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v22 v23
               -> case coe v9 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v24 v25 v26
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_568 v18
                           (coe
                              du_polys'45'transport'45''7580'_500 (coe v0)
                              (coe addInt (coe (1 :: Integer)) (coe v1))
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v2)
                                 (coe v22) (coe v24))
                              (coe
                                 MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v3) (coe v24))
                              (coe v4) (coe v5) (coe v6) (coe v7) (coe v23) (coe v26)
                              (coe MAlonzo.Code.Once.Surface.Syntax.C__'8759'__66 v18 v10)
                              (coe v21))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_578 v16
        -> case coe v9 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v17 v18 v19
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_578
                    (coe
                       du_polys'45'transport'45''7501'_384 (coe v8) (coe v19) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_594 v17 v18 v19 v20
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v21 v22
               -> case coe v9 of
                    MAlonzo.Code.Once.Type.C__'42'__126 v23 v24
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_594
                           v17 v18
                           (coe
                              du_polys'45'transport'45''7580'_500 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v21) (coe v23)
                              (coe v17) (coe v19))
                           (coe
                              du_polys'45'transport'45''7580'_500 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v22) (coe v24)
                              (coe v18) (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_606 v15 v16 v18
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v19 v20
               -> case coe v9 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_132 v21
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_606
                           v15 v16
                           (coe
                              du_polys'45'transport'45''7580'_500 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v20)
                              (coe
                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v21) (coe v9))
                              (coe v16) (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_618 v14 v16 v17
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_618 v14
                    v16
                    (coe
                       du_polys'45'transport'45''7522'_450 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v19)
                       (coe
                          MAlonzo.Code.Once.Type.C__'42'__126
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v14)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe v9))
                          (coe v14))
                       (coe v16) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_630 v16 v17
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> case coe v9 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v20 v21
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_630
                           v16
                           (coe
                              du_polys'45'transport'45''7580'_500 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v19) (coe v20)
                              (coe v16) (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_642 v16 v17
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> case coe v9 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v20 v21
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_642
                           v16
                           (coe
                              du_polys'45'transport'45''7580'_500 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v19) (coe v21)
                              (coe v16) (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_652 v15 v16
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_652
                    v15
                    (coe
                       du_polys'45'transport'45''7580'_500 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v18)
                       (coe MAlonzo.Code.Once.Type.C_Void_124) (coe v15) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arr'45'app'45'check_664 v17
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> case coe v9 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v20 v21 v22
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arr'45'app'45'check_664
                           (coe
                              du_polys'45'transport'45''7580'_500 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v19)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v20)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe MAlonzo.Code.Once.Type.C_pure_34))
                                 (coe v22))
                              (coe v10) (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_680 v15 v17 v18 v20 v21
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v22 v23
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_680
                    v15 v17 v18
                    (coe
                       du_polys'45'transport'45''7522'_450 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v23) (coe v15)
                       (coe v18) (coe v20))
                    (coe
                       du_polys'45'transport'45''7580'_500 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v22)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v15)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v9))
                       (coe v17) (coe v21))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_692 v15 v16 v22
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v23
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_692
                    v15
                    (MAlonzo.Code.Once.Parser.Module.Resolve.d_canonExpr_272
                       (coe v0) (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v16))
                    (coe
                       du_polys'45'transport'45''7580'_500 (coe v0) (coe (0 :: Integer))
                       (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
                       (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
                       (coe (0 :: Integer)) (coe v5)
                       (coe MAlonzo.Code.Once.TypeCheck.Classify.d_emptySigEffects_12)
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.d_removePoly_84 (coe v23)
                          (coe v7))
                       (coe
                          MAlonzo.Code.Once.Parser.Module.Resolve.d_canonExpr_272 (coe v0)
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v16))
                       (coe v9)
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_70
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_size_186
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_208
                                (coe v5)
                                (coe
                                   d_canonPolysCtx_6 (coe v0)
                                   (coe
                                      MAlonzo.Code.Once.TypeCheck.Classify.d_removePoly_84 (coe v23)
                                      (coe v7))))))
                       (coe
                          MAlonzo.Code.Once.Adequacy.CanonPreserveMutual.du_canon'45'pres'45''7580'_130
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_208
                             (coe v5)
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Classify.d_removePoly_84 (coe v23)
                                (coe v7)))
                          (coe v16) (coe v9)
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_70
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Classify.d_size_186
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_208
                                   (coe v5)
                                   (coe
                                      d_canonPolysCtx_6 (coe v0)
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.Classify.d_removePoly_84
                                         (coe v23) (coe v7))))))
                          (coe v0) (coe v22)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
