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

module MAlonzo.Code.Once.Adequacy.CanonReflectPolyTransport where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.Adequacy.CanonReflectMutual
import qualified MAlonzo.Code.Once.Parser.Module.Resolve
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.Adequacy.CanonReflectPolyTransport.composeMid-polys-decanon
d_composeMid'45'polys'45'decanon_30 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_composeMid'45'polys'45'decanon_30 = erased
-- Once.Adequacy.CanonReflectPolyTransport.just-inj
d_just'45'inj_58 ::
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'inj_58 = erased
-- Once.Adequacy.CanonReflectPolyTransport.n≢j
d_n'8802'j_64 ::
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_n'8802'j_64 = erased
-- Once.Adequacy.CanonReflectPolyTransport.polys-reflect-ᵍ
d_polys'45'reflect'45''7501'_86 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14
d_polys'45'reflect'45''7501'_86 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
                                v9 v10
  = du_polys'45'reflect'45''7501'_86 v8 v9 v10
du_polys'45'reflect'45''7501'_86 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14
du_polys'45'reflect'45''7501'_86 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'int_372
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'int_372
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'float_384
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'float_384
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'neg'45'int_390
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'neg'45'int_390
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'neg'45'float_402
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'neg'45'float_402
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'terminal_406
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'terminal_406
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'pair_418 v8 v9
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'42'__122 v12 v13
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'pair_418
                           (coe du_polys'45'reflect'45''7501'_86 (coe v10) (coe v12) (coe v8))
                           (coe du_polys'45'reflect'45''7501'_86 (coe v11) (coe v13) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inl_428 v7
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v10 v11
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inl_428
                           (coe du_polys'45'reflect'45''7501'_86 (coe v9) (coe v10) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inr_438 v7
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v10 v11
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inr_438
                           (coe du_polys'45'reflect'45''7501'_86 (coe v9) (coe v11) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'In_448 v6 v8
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_128 v11
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'In_448 v6
                           (coe
                              du_polys'45'reflect'45''7501'_86 (coe v10)
                              (coe
                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v11) (coe v1))
                              (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonReflectPolyTransport.polys-reflect-ᵢ
d_polys'45'reflect'45''7522'_182 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_240 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_polys'45'reflect'45''7522'_182 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 ~v9
                                 v10 v11 v12 v13
  = du_polys'45'reflect'45''7522'_182
      v0 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13
du_polys'45'reflect'45''7522'_182 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_polys'45'reflect'45''7522'_182 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                  v11
  = case coe v11 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_30
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_30
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'float_42
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'float_42
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'str_48
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'str_48
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_52
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_52
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_56
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_56
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_68 v16
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_68 v16
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_78 v17
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_78 v17
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_86 v16
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_86 v16
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_94 v18
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_94 v18
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_110 v15 v16 v17 v18 v26
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v27
               -> let v28
                        = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupPolyPrefix_170
                            (coe v7) (coe v27) in
                  coe
                    (case coe v28 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v29
                         -> case coe v29 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                -> case coe v31 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                       -> coe
                                            MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_110
                                            v15 v32 v33 v18
                                            (coe
                                               du_d'45'rec_484 (coe v0) (coe v32) (coe v33) (coe v5)
                                               (coe v9) (coe v26))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_120 v16
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v17 v18
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_120
                    (coe
                       du_polys'45'reflect'45''7580'_232 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v17) (coe v9)
                       (coe v10) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_136 v17 v18 v19 v20
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v21 v22
               -> case coe v9 of
                    MAlonzo.Code.Once.Type.C__'42'__122 v23 v24
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_136 v17 v18
                           (coe
                              du_polys'45'reflect'45''7522'_182 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v21) (coe v23)
                              (coe v17) (coe v19))
                           (coe
                              du_polys'45'reflect'45''7522'_182 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v22) (coe v24)
                              (coe v18) (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_144 v15
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_144
                    (coe
                       du_polys'45'reflect'45''7522'_182 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v17)
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_156
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_156
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_176 v16 v18 v19 v20 v21 v22
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v23 v24 v25
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_176 v16 v18 v19 v20
                    (coe
                       du_polys'45'reflect'45''7522'_182 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v24) (coe v16)
                       (coe v19) (coe v21))
                    (coe
                       du_polys'45'reflect'45''7522'_182 (coe v0)
                       (coe addInt (coe (1 :: Integer)) (coe v1))
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v2)
                          (coe v23) (coe v16))
                       (coe
                          MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v3) (coe v16))
                       (coe v4) (coe v5) (coe v6) (coe v7) (coe v25) (coe v9)
                       (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v18 v20)
                       (coe v22))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_206 v18 v19 v21 v22 v23 v24 v25 v26 v27 v28
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v29 v30 v31 v32 v33
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_206 v18 v19 v21
                    v22 v23 v24 v25
                    (coe
                       du_polys'45'reflect'45''7522'_182 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v29)
                       (coe MAlonzo.Code.Once.Type.C__'43'__124 (coe v18) (coe v19))
                       (coe v23) (coe v26))
                    (coe
                       du_polys'45'reflect'45''7522'_182 (coe v0)
                       (coe addInt (coe (1 :: Integer)) (coe v1))
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v2)
                          (coe v30) (coe v18))
                       (coe
                          MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v3) (coe v18))
                       (coe v4) (coe v5) (coe v6) (coe v7) (coe v31) (coe v9)
                       (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v21 v24)
                       (coe v27))
                    (coe
                       du_polys'45'reflect'45''7522'_182 (coe v0)
                       (coe addInt (coe (1 :: Integer)) (coe v1))
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v2)
                          (coe v32) (coe v19))
                       (coe
                          MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v3) (coe v19))
                       (coe v4) (coe v5) (coe v6) (coe v7) (coe v33) (coe v9)
                       (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v22 v25)
                       (coe v28))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_220 v16 v17 v19 v20
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v21 v22 v23
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_220 v16
                    v17
                    (coe
                       du_polys'45'reflect'45''7522'_182 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v22)
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v16) (coe v19))
                    (coe
                       du_polys'45'reflect'45''7522'_182 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v23)
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v17) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_234 v16 v17 v19 v20
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v21 v22 v23
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_234
                    v16 v17
                    (coe
                       du_polys'45'reflect'45''7522'_182 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v22)
                       (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v16) (coe v19))
                    (coe
                       du_polys'45'reflect'45''7522'_182 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v23)
                       (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v17) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_248 v16 v17 v19 v20
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v21 v22 v23
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_248
                    v16 v17
                    (coe
                       du_polys'45'reflect'45''7522'_182 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v22)
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v16) (coe v19))
                    (coe
                       du_polys'45'reflect'45''7522'_182 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v23)
                       (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v17) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_262 v16 v17 v19 v20
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v21 v22 v23
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_262
                    v16 v17
                    (coe
                       du_polys'45'reflect'45''7522'_182 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v22)
                       (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v16) (coe v19))
                    (coe
                       du_polys'45'reflect'45''7522'_182 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v23)
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v17) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_276 v16 v17 v19 v20
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v21 v22 v23
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_276 v16
                    v17
                    (coe
                       du_polys'45'reflect'45''7522'_182 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v22)
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v16) (coe v19))
                    (coe
                       du_polys'45'reflect'45''7522'_182 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v23)
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v17) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_286 v15 v16
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_286 v15
                    (coe
                       du_polys'45'reflect'45''7522'_182 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v18) (coe v9)
                       (coe v15) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_298 v15 v16 v17
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_298 v15 v16
                    (coe
                       du_polys'45'reflect'45''7522'_182 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v19)
                       (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v9) (coe v15))
                       (coe v16) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_310 v14 v16 v17
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_310 v14 v16
                    (coe
                       du_polys'45'reflect'45''7522'_182 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v19)
                       (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v14) (coe v9))
                       (coe v16) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_320 v14 v15 v16
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_320 v14
                    v15
                    (coe
                       du_polys'45'reflect'45''7522'_182 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v18) (coe v14)
                       (coe v15) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_332 v14 v16 v17
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_332
                    v14 v16
                    (coe
                       du_polys'45'reflect'45''7522'_182 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v19)
                       (coe
                          MAlonzo.Code.Once.Type.C__'42'__122
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v14)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe v9))
                          (coe v14))
                       (coe v16) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_350 v15 v17 v18 v19 v21 v22
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v23 v24
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_350 v15 v17 v18 v19
                    (coe
                       du_polys'45'reflect'45''7522'_182 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v23)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v15)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v17)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v9))
                       (coe v18) (coe v21))
                    (coe
                       du_polys'45'reflect'45''7580'_232 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v24) (coe v15)
                       (coe v19) (coe v22))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_366 v15 v17 v18 v20 v21
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v22 v23
               -> case coe v9 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v24 v25 v26
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_366 v15 v17 v18
                           (coe
                              du_polys'45'reflect'45''7522'_182 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v22)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v15)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe MAlonzo.Code.Once.Type.C_eff_36))
                                 (coe v26))
                              (coe v17) (coe v20))
                           (coe
                              du_polys'45'reflect'45''7580'_232 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v23) (coe v15)
                              (coe v18) (coe v21))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonReflectPolyTransport.polys-reflect-ᵐ
d_polys'45'reflect'45''7504'_208 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_240 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18
d_polys'45'reflect'45''7504'_208 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8 ~v9 v10 v11 ~v12 v13 v14
  = du_polys'45'reflect'45''7504'_208 v10 v11 v13 v14
du_polys'45'reflect'45''7504'_208 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18
du_polys'45'reflect'45''7504'_208 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'id_456
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'id_456
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'fst_466
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'fst_466
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'snd_476
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'snd_476
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'terminal_484
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'terminal_484
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'initial_492
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'initial_492
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inl_502
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inl_502
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inr_512
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inr_512
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'compose_528 v8 v12 v13
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> case coe v14 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'compose_528 v8
                           (coe
                              du_polys'45'reflect'45''7504'_208 (coe v17) (coe v8) (coe v2)
                              (coe v12))
                           (coe
                              du_polys'45'reflect'45''7504'_208 (coe v15) (coe v1) (coe v8)
                              (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'case_544 v11 v12
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> case coe v13 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
                      -> case coe v1 of
                           MAlonzo.Code.Once.Type.C__'43'__124 v17 v18
                             -> coe
                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'case_544
                                  (coe
                                     du_polys'45'reflect'45''7504'_208 (coe v16) (coe v17) (coe v2)
                                     (coe v11))
                                  (coe
                                     du_polys'45'reflect'45''7504'_208 (coe v14) (coe v18) (coe v2)
                                     (coe v12))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'pair_558 v10 v11
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> case coe v12 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'42'__122 v16 v17
                             -> coe
                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'pair_558
                                  (coe
                                     du_polys'45'reflect'45''7504'_208 (coe v15) (coe v1) (coe v16)
                                     (coe v10))
                                  (coe
                                     du_polys'45'reflect'45''7504'_208 (coe v13) (coe v1) (coe v17)
                                     (coe v11))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'curry_570 v9
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'curry_570
                           (coe
                              du_polys'45'reflect'45''7504'_208 (coe v11)
                              (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v1) (coe v12))
                              (coe v14) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'cata_584 v9 v11
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_128 v14
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'cata_584 v9
                           (coe
                              du_polys'45'reflect'45''7504'_208 (coe v13)
                              (coe
                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v14) (coe v2))
                              (coe v2) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_596 v9
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_596
             (coe du_polys'45'reflect'45''7501'_86 (coe v0) (coe v2) (coe v9))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named_608 v12 v13
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named_608 v12 v13
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named'45'resolved_620 v10 v11
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named'45'resolved_620
             v10 v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonReflectPolyTransport.polys-reflect-ᶜ
d_polys'45'reflect'45''7580'_232 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_240 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
d_polys'45'reflect'45''7580'_232 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 ~v9
                                 v10 v11 v12 v13
  = du_polys'45'reflect'45''7580'_232
      v0 v1 v2 v3 v4 v5 v6 v7 v10 v11 v12 v13
du_polys'45'reflect'45''7580'_232 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
du_polys'45'reflect'45''7580'_232 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
                                  v11
  = case coe v11 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632 v17
        -> case coe v9 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v18 v19 v20
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632
                    (coe
                       du_polys'45'reflect'45''7504'_208 (coe v8) (coe v18) (coe v20)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_642 v16
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_642
             (coe
                du_polys'45'reflect'45''7522'_182 (coe v0) (coe v1) (coe v2)
                (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
                (coe v10) (coe v16))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_660 v18 v21
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v22 v23
               -> case coe v9 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v24 v25 v26
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_660 v18
                           (coe
                              du_polys'45'reflect'45''7580'_232 (coe v0)
                              (coe addInt (coe (1 :: Integer)) (coe v1))
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v2)
                                 (coe v22) (coe v24))
                              (coe
                                 MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v3) (coe v24))
                              (coe v4) (coe v5) (coe v6) (coe v7) (coe v23) (coe v26)
                              (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v18 v10)
                              (coe v21))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672 v17
        -> case coe v9 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v18 v19 v20
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672
                    (coe du_polys'45'reflect'45''7501'_86 (coe v8) (coe v20) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'closed'45'lift_684 v17 v18
        -> case coe v9 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v19 v20 v21
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'closed'45'lift_684 v17
                    (coe
                       du_polys'45'reflect'45''7522'_182 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v21)
                       (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v1))
                       (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_700 v17 v18 v19 v20
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v21 v22
               -> case coe v9 of
                    MAlonzo.Code.Once.Type.C__'42'__122 v23 v24
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_700
                           v17 v18
                           (coe
                              du_polys'45'reflect'45''7580'_232 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v21) (coe v23)
                              (coe v17) (coe v19))
                           (coe
                              du_polys'45'reflect'45''7580'_232 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v22) (coe v24)
                              (coe v18) (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_712 v15 v16 v18
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v19 v20
               -> case coe v9 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_128 v21
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_712
                           v15 v16
                           (coe
                              du_polys'45'reflect'45''7580'_232 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v20)
                              (coe
                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v21) (coe v9))
                              (coe v16) (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_724 v14 v16 v17
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_724 v14
                    v16
                    (coe
                       du_polys'45'reflect'45''7522'_182 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v19)
                       (coe
                          MAlonzo.Code.Once.Type.C__'42'__122
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v14)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe v9))
                          (coe v14))
                       (coe v16) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_736 v16 v17
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> case coe v9 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v20 v21
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_736
                           v16
                           (coe
                              du_polys'45'reflect'45''7580'_232 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v19) (coe v20)
                              (coe v16) (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_748 v16 v17
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> case coe v9 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v20 v21
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_748
                           v16
                           (coe
                              du_polys'45'reflect'45''7580'_232 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v19) (coe v21)
                              (coe v16) (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_758 v15 v16
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_758
                    v15
                    (coe
                       du_polys'45'reflect'45''7580'_232 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v18)
                       (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v15) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_770 v17
        -> case coe v9 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v18 v19 v20
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_770
                    (coe
                       du_polys'45'reflect'45''7580'_232 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v18)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v20))
                       (coe v10) (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_786 v15 v17 v18 v20 v21
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v22 v23
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_786
                    v15 v17 v18
                    (coe
                       du_polys'45'reflect'45''7522'_182 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v23) (coe v15)
                       (coe v18) (coe v20))
                    (coe
                       du_polys'45'reflect'45''7580'_232 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v5) (coe v6) (coe v7) (coe v22)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v15)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v9))
                       (coe v17) (coe v21))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_800 v15 v16 v17 v24
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v25
               -> let v26
                        = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupPolyPrefix_170
                            (coe v7) (coe v25) in
                  coe
                    (case coe v26 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v27
                         -> case coe v27 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                -> case coe v29 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                       -> coe
                                            MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_800
                                            v15 v30 v31
                                            (coe
                                               du_d'45'rec_1188 (coe v0) (coe v30) (coe v31)
                                               (coe v5) (coe v9) (coe v24))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonReflectPolyTransport._.eqJ
d_eqJ_466 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_240 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eqJ_466 = erased
-- Once.Adequacy.CanonReflectPolyTransport._.lp-rec
d_lp'45'rec_468 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_240 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lp'45'rec_468 = erased
-- Once.Adequacy.CanonReflectPolyTransport._.dC1
d_dC1_472 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_240 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
d_dC1_472 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
          ~v26 ~v27 v28
  = du_dC1_472 v28
du_dC1_472 ::
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
du_dC1_472 v0 = coe v0
-- Once.Adequacy.CanonReflectPolyTransport._.dC2
d_dC2_478 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_240 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
d_dC2_478 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
          ~v26 ~v27 v28
  = du_dC2_478 v28
du_dC2_478 ::
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
du_dC2_478 v0 = coe v0
-- Once.Adequacy.CanonReflectPolyTransport._.d-rec
d_d'45'rec_484 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_240 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
d_d'45'rec_484 v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
               ~v13 ~v14 ~v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
               ~v26 ~v27 v28
  = du_d'45'rec_484 v0 v4 v5 v12 v16 v28
du_d'45'rec_484 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
du_d'45'rec_484 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.CanonReflectMutual.du_canon'45'reflects'45''7580'_1386
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
         (coe v3) (coe v2))
      (coe v4)
      (coe
         MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
               (coe v3) (coe v2))))
      (coe v0) (coe v1)
      (coe
         du_polys'45'reflect'45''7580'_232 (coe v0) (coe (0 :: Integer))
         (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
         (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
         (coe (0 :: Integer)) (coe v3)
         (coe MAlonzo.Code.Once.TypeCheck.Classify.d_emptySigEffects_12)
         (coe v2)
         (coe
            MAlonzo.Code.Once.Parser.Module.Resolve.d_canonExpr_346 (coe v0)
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v1))
         (coe v4)
         (coe
            MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                  (coe v3) (coe v2))))
         (coe v5))
-- Once.Adequacy.CanonReflectPolyTransport._.eqJ
d_eqJ_1170 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_240 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eqJ_1170 = erased
-- Once.Adequacy.CanonReflectPolyTransport._.lp-rec
d_lp'45'rec_1172 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_240 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lp'45'rec_1172 = erased
-- Once.Adequacy.CanonReflectPolyTransport._.dC1
d_dC1_1176 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_240 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
d_dC1_1176 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
           v26
  = du_dC1_1176 v26
du_dC1_1176 ::
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
du_dC1_1176 v0 = coe v0
-- Once.Adequacy.CanonReflectPolyTransport._.dC2
d_dC2_1182 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_240 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
d_dC2_1182 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
           v26
  = du_dC2_1182 v26
du_dC2_1182 ::
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
du_dC2_1182 v0 = coe v0
-- Once.Adequacy.CanonReflectPolyTransport._.d-rec
d_d'45'rec_1188 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_PolyType_240 ->
   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
d_d'45'rec_1188 v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
                ~v13 ~v14 ~v15 v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25 v26
  = du_d'45'rec_1188 v0 v4 v5 v12 v16 v26
du_d'45'rec_1188 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
du_d'45'rec_1188 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Adequacy.CanonReflectMutual.du_canon'45'reflects'45''7580'_1386
      (coe
         MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
         (coe v3) (coe v2))
      (coe v4)
      (coe
         MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
         (coe
            MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
               (coe v3) (coe v2))))
      (coe v0) (coe v1)
      (coe
         du_polys'45'reflect'45''7580'_232 (coe v0) (coe (0 :: Integer))
         (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
         (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
         (coe (0 :: Integer)) (coe v3)
         (coe MAlonzo.Code.Once.TypeCheck.Classify.d_emptySigEffects_12)
         (coe v2)
         (coe
            MAlonzo.Code.Once.Parser.Module.Resolve.d_canonExpr_346 (coe v0)
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v1))
         (coe v4)
         (coe
            MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
               (coe
                  MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                  (coe v3) (coe v2))))
         (coe v5))
