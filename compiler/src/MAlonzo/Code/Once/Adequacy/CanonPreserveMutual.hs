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
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
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
  MAlonzo.Code.Once.Type.T_Type_108 -> T_PolyInB_16 -> T_PolyInB_16
d_poly'45'ext_82 = erased
-- Once.Adequacy.CanonPreserveMutual.canon-pres-ᵢ
d_canon'45'pres'45''7522'_104 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
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
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_canon'45'pres'45''7522'_104 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_22
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_22
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'float_34
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'float_34
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'str_40
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'str_40
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_44
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_44
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_48
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_48
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_60 v10
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_60 v10
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_70 v11
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_70 v11
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_78 v10
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_78 v10
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_86 v12
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
                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_86 v12
                       else coe
                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_78 v12)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_102 v9 v10 v11 v12 v18 v20
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_102
             v9 v10 v11 v12 v18 v20
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_112 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v11 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_112
                    (coe
                       du_canon'45'pres'45''7580'_116 (coe v0) (coe v11) (coe v2) (coe v3)
                       (coe v4) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_128 v11 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v15 v16
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__122 v17 v18
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_128 v11 v12
                           (coe
                              du_canon'45'pres'45''7522'_104 (coe v0) (coe v15) (coe v17)
                              (coe v11) (coe v4) (coe v13))
                           (coe
                              du_canon'45'pres'45''7522'_104 (coe v0) (coe v16) (coe v18)
                              (coe v12) (coe v4) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_136 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_136
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v11)
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v3) (coe v4) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_148
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_148
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_168 v10 v12 v13 v14 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v17 v18 v19
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_168 v10 v12 v13 v14
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_198 v12 v13 v15 v16 v17 v18 v19 v20 v21 v22
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v23 v24 v25 v26 v27
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_198 v12 v13 v15
                    v16 v17 v18 v19
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v23)
                       (coe MAlonzo.Code.Once.Type.C__'43'__124 (coe v12) (coe v13))
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_212 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v15 v16 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_212 v10
                    v11
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v16)
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10) (coe v4)
                       (coe v13))
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v17)
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v11) (coe v4)
                       (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_226 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v15 v16 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_226
                    v10 v11
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v16)
                       (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v10) (coe v4)
                       (coe v13))
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v17)
                       (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v11) (coe v4)
                       (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_240 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v15 v16 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_240
                    v10 v11
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v16)
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10) (coe v4)
                       (coe v13))
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v17)
                       (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v11) (coe v4)
                       (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_254 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v15 v16 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_254
                    v10 v11
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v16)
                       (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v10) (coe v4)
                       (coe v13))
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v17)
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v11) (coe v4)
                       (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_268 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v15 v16 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_268 v10
                    v11
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v16)
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10) (coe v4)
                       (coe v13))
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v17)
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v11) (coe v4)
                       (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_278 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_278 v9
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v12) (coe v2) (coe v9)
                       (coe v4) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_290 v9 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_290 v9 v10
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v13)
                       (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v2) (coe v9))
                       (coe v10) (coe v4) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_302 v8 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_302 v8 v10
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v13)
                       (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v8) (coe v2))
                       (coe v10) (coe v4) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_312 v8 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_312 v8
                    v9
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v12) (coe v8) (coe v9)
                       (coe v4) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_324 v8 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_324
                    v8 v10
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v13)
                       (coe
                          MAlonzo.Code.Once.Type.C__'42'__122
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v8)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe v2))
                          (coe v8))
                       (coe v10) (coe v4) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_342 v9 v11 v12 v13 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_342 v9 v11 v12 v13
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v17)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v9)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v11)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v2))
                       (coe v12) (coe v4) (coe v15))
                    (coe
                       du_canon'45'pres'45''7580'_116 (coe v0) (coe v18) (coe v9)
                       (coe v13) (coe v4) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_358 v9 v11 v12 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v18 v19 v20
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_358 v9 v11 v12
                           (coe
                              du_canon'45'pres'45''7522'_104 (coe v0) (coe v16)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v9)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe MAlonzo.Code.Once.Type.C_eff_36))
                                 (coe v20))
                              (coe v11) (coe v4) (coe v14))
                           (coe
                              du_canon'45'pres'45''7580'_116 (coe v0) (coe v17) (coe v9)
                              (coe v12) (coe v4) (coe v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonPreserveMutual.canon-pres-ᶜ
d_canon'45'pres'45''7580'_116 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_PolyInB_16 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
d_canon'45'pres'45''7580'_116 v0 v1 v2 v3 v4 ~v5 ~v6 v7
  = du_canon'45'pres'45''7580'_116 v0 v1 v2 v3 v4 v7
du_canon'45'pres'45''7580'_116 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
du_canon'45'pres'45''7580'_116 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'check_366
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'check_366
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'check_376
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'check_376
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'check_386
        -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'check_386
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'morph'45'check_394
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'morph'45'check_394
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'morph'45'check_402
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'morph'45'check_402
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'morph'45'check_412
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'morph'45'check_412
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'morph'45'check_422
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'morph'45'check_422
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check_442 v10 v13 v14 v16 v17
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v20 v21
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v22 v23 v24
                             -> case coe v23 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v25 v26
                                    -> coe
                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check_442
                                         v10 v13 v14
                                         (coe
                                            du_canon'45'pres'45''7580'_116 (coe v0) (coe v21)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                               (coe v10)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v26))
                                               (coe v24))
                                            (coe v13) (coe v4) (coe v16))
                                         (coe
                                            du_canon'45'pres'45''7580'_116 (coe v0) (coe v19)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                               (coe v22)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v26))
                                               (coe v10))
                                            (coe v14) (coe v4) (coe v17))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case'45'copair'45'check_462 v13 v14 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v19 v20
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v21 v22 v23
                             -> case coe v21 of
                                  MAlonzo.Code.Once.Type.C__'43'__124 v24 v25
                                    -> case coe v22 of
                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50 v26 v27
                                           -> coe
                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case'45'copair'45'check_462
                                                v13 v14
                                                (coe
                                                   du_canon'45'pres'45''7580'_116 (coe v0) (coe v20)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                      (coe v24)
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                         (coe v27))
                                                      (coe v23))
                                                   (coe v13) (coe v4) (coe v15))
                                                (coe
                                                   du_canon'45'pres'45''7580'_116 (coe v0) (coe v18)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                      (coe v25)
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                         (coe v27))
                                                      (coe v23))
                                                   (coe v14) (coe v4) (coe v16))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'morph'45'check_480 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v20 v21 v22
                             -> case coe v22 of
                                  MAlonzo.Code.Once.Type.C__'42'__122 v23 v24
                                    -> coe
                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'morph'45'check_480
                                         v12 v13
                                         (coe
                                            du_canon'45'pres'45''7580'_116 (coe v0) (coe v19)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                               (coe v20)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                  (coe MAlonzo.Code.Once.Type.C_pure_34))
                                               (coe v23))
                                            (coe v12) (coe v4) (coe v14))
                                         (coe
                                            du_canon'45'pres'45''7580'_116 (coe v0) (coe v17)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                               (coe v20)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                  (coe MAlonzo.Code.Once.Type.C_pure_34))
                                               (coe v24))
                                            (coe v13) (coe v4) (coe v15))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'curry'45'check_494 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v15 v16 v17
                      -> case coe v17 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v18 v19 v20
                             -> coe
                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'curry'45'check_494
                                  (coe
                                     du_canon'45'pres'45''7580'_116 (coe v0) (coe v14)
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'42'__122 (coe v15) (coe v18))
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                                           (coe MAlonzo.Code.Once.Type.C_pure_34))
                                        (coe v20))
                                     (coe v3) (coe v4) (coe v12))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'cata'45'check_506 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v15 v16 v17
                      -> case coe v15 of
                           MAlonzo.Code.Once.Type.C_μ'45'type_128 v18
                             -> case coe v16 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v19 v20
                                    -> coe
                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'cata'45'check_506
                                         v11
                                         (coe
                                            du_canon'45'pres'45''7580'_116
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                                  (coe v0))
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364
                                                  (coe v0)))
                                            (coe v14)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                               (coe
                                                  MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                  (coe v18) (coe v17))
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v20))
                                               (coe v17))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                                        (coe v0))
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364
                                                        (coe v0)))))
                                            (coe v4) (coe v12))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_516 v10
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_516
             (coe
                du_canon'45'pres'45''7522'_104 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v10))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_534 v12 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v16 v17
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v18 v19 v20
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_534 v12
                           (coe
                              du_canon'45'pres'45''7580'_116
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_550 v11 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v15 v16
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__122 v17 v18
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_550
                           v11 v12
                           (coe
                              du_canon'45'pres'45''7580'_116 (coe v0) (coe v15) (coe v17)
                              (coe v11) (coe v4) (coe v13))
                           (coe
                              du_canon'45'pres'45''7580'_116 (coe v0) (coe v16) (coe v18)
                              (coe v12) (coe v4) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_560 v9 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_128 v14
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_560
                           v9 v10
                           (coe
                              du_canon'45'pres'45''7580'_116 (coe v0) (coe v13)
                              (coe
                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v14) (coe v2))
                              (coe v9) (coe v4) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_572 v8 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_572 v8
                    v10
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v13)
                       (coe
                          MAlonzo.Code.Once.Type.C__'42'__122
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v8)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe v2))
                          (coe v8))
                       (coe v10) (coe v4) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_584 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v14 v15
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_584
                           v10
                           (coe
                              du_canon'45'pres'45''7580'_116 (coe v0) (coe v13) (coe v14)
                              (coe v10) (coe v4) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_596 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v14 v15
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_596
                           v10
                           (coe
                              du_canon'45'pres'45''7580'_116 (coe v0) (coe v13) (coe v15)
                              (coe v10) (coe v4) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_606 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_606
                    v9
                    (coe
                       du_canon'45'pres'45''7580'_116 (coe v0) (coe v12)
                       (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v9) (coe v4)
                       (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_618 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_618
                    (coe
                       du_canon'45'pres'45''7580'_116 (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v12)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v14))
                       (coe v3) (coe v4) (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_634 v9 v11 v12 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_634
                    v9 v11 v12
                    (coe
                       du_canon'45'pres'45''7522'_104 (coe v0) (coe v17) (coe v9)
                       (coe v12) (coe v4) (coe v14))
                    (coe
                       du_canon'45'pres'45''7580'_116 (coe v0) (coe v16)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v9)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v2))
                       (coe v11) (coe v4) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_648 v9 v10 v11 v18
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_648
             v9 v10 v11 v18
      _ -> MAlonzo.RTE.mazUnreachableError
