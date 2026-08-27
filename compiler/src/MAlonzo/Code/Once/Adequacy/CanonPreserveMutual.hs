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

module MAlonzo.Code.Once.Adequacy.CanonPreserveMutual where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Once.Adequacy.CanonPreserve
import qualified MAlonzo.Code.Once.Parser.Module.Resolve
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.Adequacy.CanonPreserveMutual.Names⊆
d_Names'8838'_6 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> ()
d_Names'8838'_6 = erased
-- Once.Adequacy.CanonPreserveMutual.PolyInB
d_PolyInB_16 a0 a1 = ()
data T_PolyInB_16 = C_mkPIB_38
-- Once.Adequacy.CanonPreserveMutual.PolyInB.app
d_app_36 ::
  T_PolyInB_16 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_244 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_app_36 = erased
-- Once.Adequacy.CanonPreserveMutual.or-l
d_or'45'l_44 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_or'45'l_44 = erased
-- Once.Adequacy.CanonPreserveMutual.⊆ᵇ-weaken
d_'8838''7495''45'weaken_50 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8838''7495''45'weaken_50 = erased
-- Once.Adequacy.CanonPreserveMutual.poly-ext
d_poly'45'ext_82 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> T_PolyInB_16 -> T_PolyInB_16
d_poly'45'ext_82 = erased
-- Once.Adequacy.CanonPreserveMutual.canon-pres-ᵢ
d_canon'45'pres'45''7522'_104 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_PolyInB_16 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_canon'45'pres'45''7522'_104 v0 v1 v2 v3 v4 ~v5 ~v6 v7
  = du_canon'45'pres'45''7522'_104 v0 v1 v2 v3 v4 v7
du_canon'45'pres'45''7522'_104 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_canon'45'pres'45''7522'_104 v0 v1 v2 v3 v4 v5
  = case coe v5 of
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_68 v10
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_68 v10
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_78 v11
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_78 v11
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_86 v10
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_86 v10
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_94 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v13
               -> let v14
                        = MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                            (coe
                               MAlonzo.Code.Once.Parser.Module.Resolve.d_elemStr_194 (coe v13)
                               (coe v4))
                            (coe
                               MAlonzo.Code.Once.Parser.Module.Resolve.d_isBuiltinName_192
                               (coe v13)) in
                  coe
                    (if coe v14
                       then coe
                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_94 v12
                       else coe
                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_86 v12)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_110 v9 v10 v11 v12 v20
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_110
             v9 v10 v11 v12 v20
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_120 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v11 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_120
                    (coe
                       du_canon'45'pres'45''7580'_130 (coe v0) (coe v11) (coe v2) (coe v3)
                       (coe v4) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_136 v11 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v15 v16
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__126 v17 v18
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_136 v11 v12
                           (coe
                              du_canon'45'pres'45''7522'_104 (coe v0) (coe v15) (coe v17)
                              (coe v11) (coe v4) (coe v13))
                           (coe
                              du_canon'45'pres'45''7522'_104 (coe v0) (coe v16) (coe v18)
                              (coe v12) (coe v4) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_144 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_144
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v11)
                       (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v3) (coe v4) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_156
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_156
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_176 v10 v12 v13 v14 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v17 v18 v19
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_176 v10 v12 v13 v14
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v18) (coe v10)
                       (coe v13) (coe v4) (coe v15))
                    (coe
                       du_canon'45'pres'45''7522'_104
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402 (coe v0)
                          (coe v17) (coe v10))
                       (coe v19) (coe v2)
                       (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v12 v14)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v17) (coe v4))
                       (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_206 v12 v13 v15 v16 v17 v18 v19 v20 v21 v22
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v23 v24 v25 v26 v27
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_206 v12 v13 v15
                    v16 v17 v18 v19
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v23)
                       (coe MAlonzo.Code.Once.Type.C__'43'__128 (coe v12) (coe v13))
                       (coe v17) (coe v4) (coe v20))
                    (coe
                       du_canon'45'pres'45''7522'_104
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402 (coe v0)
                          (coe v24) (coe v12))
                       (coe v25) (coe v2)
                       (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v15 v18)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v24) (coe v4))
                       (coe v21))
                    (coe
                       du_canon'45'pres'45''7522'_104
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402 (coe v0)
                          (coe v26) (coe v13))
                       (coe v27) (coe v2)
                       (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v16 v19)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v26) (coe v4))
                       (coe v22))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_220 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v15 v16 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_220 v10
                    v11
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v16)
                       (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10) (coe v4)
                       (coe v13))
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v17)
                       (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v11) (coe v4)
                       (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_234 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v15 v16 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_234
                    v10 v11
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v16)
                       (coe MAlonzo.Code.Once.Type.C_Float_138) (coe v10) (coe v4)
                       (coe v13))
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v17)
                       (coe MAlonzo.Code.Once.Type.C_Float_138) (coe v11) (coe v4)
                       (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_248 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v15 v16 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_248
                    v10 v11
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v16)
                       (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10) (coe v4)
                       (coe v13))
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v17)
                       (coe MAlonzo.Code.Once.Type.C_Float_138) (coe v11) (coe v4)
                       (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_262 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v15 v16 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_262
                    v10 v11
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v16)
                       (coe MAlonzo.Code.Once.Type.C_Float_138) (coe v10) (coe v4)
                       (coe v13))
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v17)
                       (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v11) (coe v4)
                       (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_276 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v15 v16 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_276 v10
                    v11
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v16)
                       (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10) (coe v4)
                       (coe v13))
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v17)
                       (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v11) (coe v4)
                       (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_286 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_286 v9
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v12) (coe v2) (coe v9)
                       (coe v4) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_298 v9 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_298 v9 v10
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v13)
                       (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v2) (coe v9))
                       (coe v10) (coe v4) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_310 v8 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_310 v8 v10
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v13)
                       (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v8) (coe v2))
                       (coe v10) (coe v4) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_320 v8 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_320 v8
                    v9
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v12) (coe v8) (coe v9)
                       (coe v4) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_332 v8 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_332
                    v8 v10
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v13)
                       (coe
                          MAlonzo.Code.Once.Type.C__'42'__126
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v8)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe v2))
                          (coe v8))
                       (coe v10) (coe v4) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_350 v9 v11 v12 v13 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_350 v9 v11 v12 v13
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v17)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v9)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v11)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v2))
                       (coe v12) (coe v4) (coe v15))
                    (coe
                       du_canon'45'pres'45''7580'_130 (coe v0) (coe v18) (coe v9)
                       (coe v13) (coe v4) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_366 v9 v11 v12 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v18 v19 v20
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_366 v9 v11 v12
                           (coe
                              du_canon'45'pres'45''7522'_104 (coe v0) (coe v16)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v9)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe MAlonzo.Code.Once.Type.C_eff_36))
                                 (coe v20))
                              (coe v11) (coe v4) (coe v14))
                           (coe
                              du_canon'45'pres'45''7580'_130 (coe v0) (coe v17) (coe v9)
                              (coe v12) (coe v4) (coe v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonPreserveMutual.canon-pres-ᵐ
d_canon'45'pres'45''7504'_118 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_PolyInB_16 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18
d_canon'45'pres'45''7504'_118 ~v0 v1 v2 ~v3 v4 v5 ~v6 ~v7 v8
  = du_canon'45'pres'45''7504'_118 v1 v2 v4 v5 v8
du_canon'45'pres'45''7504'_118 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18
du_canon'45'pres'45''7504'_118 v0 v1 v2 v3 v4
  = case coe v4 of
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'compose_528 v9 v13 v14
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'compose_528 v9
                           (coe
                              du_canon'45'pres'45''7504'_118 (coe v18) (coe v9) (coe v2) (coe v3)
                              (coe v13))
                           (coe
                              du_canon'45'pres'45''7504'_118 (coe v16) (coe v1) (coe v9) (coe v3)
                              (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'case_544 v12 v13
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> case coe v14 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
                      -> case coe v1 of
                           MAlonzo.Code.Once.Type.C__'43'__128 v18 v19
                             -> coe
                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'case_544
                                  (coe
                                     du_canon'45'pres'45''7504'_118 (coe v17) (coe v18) (coe v2)
                                     (coe v3) (coe v12))
                                  (coe
                                     du_canon'45'pres'45''7504'_118 (coe v15) (coe v19) (coe v2)
                                     (coe v3) (coe v13))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'pair_558 v11 v12
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> case coe v13 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'42'__126 v17 v18
                             -> coe
                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'pair_558
                                  (coe
                                     du_canon'45'pres'45''7504'_118 (coe v16) (coe v1) (coe v17)
                                     (coe v3) (coe v11))
                                  (coe
                                     du_canon'45'pres'45''7504'_118 (coe v14) (coe v1) (coe v18)
                                     (coe v3) (coe v12))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'curry_570 v10
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v13 v14 v15
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'curry_570
                           (coe
                              du_canon'45'pres'45''7504'_118 (coe v12)
                              (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v1) (coe v13))
                              (coe v15) (coe v3) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'cata_584 v10 v12
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_132 v15
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'cata_584 v10
                           (coe
                              du_canon'45'pres'45''7504'_118 (coe v14)
                              (coe
                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v15) (coe v2))
                              (coe v2) (coe v3) (coe v12))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_596 v10
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_596
             (coe
                MAlonzo.Code.Once.Adequacy.CanonPreserve.du_pres'45''7501'_710
                (coe v0) (coe v2) (coe v10))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named_608 v13 v14
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v15
               -> let v16
                        = MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                            (coe
                               MAlonzo.Code.Once.Parser.Module.Resolve.d_elemStr_194 (coe v15)
                               (coe v3))
                            (coe
                               MAlonzo.Code.Once.Parser.Module.Resolve.d_isBuiltinName_192
                               (coe v15)) in
                  coe
                    (if coe v16
                       then coe
                              MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named_608 v13 v14
                       else coe
                              MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named'45'resolved_620
                              v13 v14)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named'45'resolved_620 v11 v12
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named'45'resolved_620
             v11 v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonPreserveMutual.canon-pres-ᶜ
d_canon'45'pres'45''7580'_130 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_PolyInB_16 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
d_canon'45'pres'45''7580'_130 v0 v1 v2 v3 v4 ~v5 ~v6 v7
  = du_canon'45'pres'45''7580'_130 v0 v1 v2 v3 v4 v7
du_canon'45'pres'45''7580'_130 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
du_canon'45'pres'45''7580'_130 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v12 v13 v14
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632
                    (coe
                       du_canon'45'pres'45''7504'_118 (coe v1) (coe v12) (coe v14)
                       (coe v4) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_642 v10
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_642
             (coe
                du_canon'45'pres'45''7522'_104 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v10))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_660 v12 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v16 v17
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v18 v19 v20
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_660 v12
                           (coe
                              du_canon'45'pres'45''7580'_130
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402 (coe v0)
                                 (coe v16) (coe v18))
                              (coe v17) (coe v20)
                              (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v12 v3)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v16) (coe v4))
                              (coe v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v12 v13 v14
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672
                    (coe
                       MAlonzo.Code.Once.Adequacy.CanonPreserve.du_pres'45''7501'_710
                       (coe v1) (coe v14) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_688 v11 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v15 v16
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__126 v17 v18
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_688
                           v11 v12
                           (coe
                              du_canon'45'pres'45''7580'_130 (coe v0) (coe v15) (coe v17)
                              (coe v11) (coe v4) (coe v13))
                           (coe
                              du_canon'45'pres'45''7580'_130 (coe v0) (coe v16) (coe v18)
                              (coe v12) (coe v4) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_700 v9 v10 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_132 v15
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_700
                           v9 v10
                           (coe
                              du_canon'45'pres'45''7580'_130 (coe v0) (coe v14)
                              (coe
                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v15) (coe v2))
                              (coe v10) (coe v4) (coe v12))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_712 v8 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_712 v8
                    v10
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v13)
                       (coe
                          MAlonzo.Code.Once.Type.C__'42'__126
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v8)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe v2))
                          (coe v8))
                       (coe v10) (coe v4) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_724 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v14 v15
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_724
                           v10
                           (coe
                              du_canon'45'pres'45''7580'_130 (coe v0) (coe v13) (coe v14)
                              (coe v10) (coe v4) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_736 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v14 v15
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_736
                           v10
                           (coe
                              du_canon'45'pres'45''7580'_130 (coe v0) (coe v13) (coe v15)
                              (coe v10) (coe v4) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_746 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_746
                    v9
                    (coe
                       du_canon'45'pres'45''7580'_130 (coe v0) (coe v12)
                       (coe MAlonzo.Code.Once.Type.C_Void_124) (coe v9) (coe v4)
                       (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_758 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v12 v13 v14
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_758
                    (coe
                       du_canon'45'pres'45''7580'_130 (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v12)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v14))
                       (coe v3) (coe v4) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_774 v9 v11 v12 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_774
                    v9 v11 v12
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v17) (coe v9)
                       (coe v12) (coe v4) (coe v14))
                    (coe
                       du_canon'45'pres'45''7580'_130 (coe v0) (coe v16)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v9)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v2))
                       (coe v11) (coe v4) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_788 v9 v10 v11 v18
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_788
             v9 v10 v11 v18
      _ -> MAlonzo.RTE.mazUnreachableError
