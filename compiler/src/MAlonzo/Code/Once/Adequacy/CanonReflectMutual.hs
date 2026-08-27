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

module MAlonzo.Code.Once.Adequacy.CanonReflectMutual where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Once.Parser.Module.Resolve
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.Adequacy.CanonReflectMutual.t≢f
d_t'8802'f_6 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_t'8802'f_6 = erased
-- Once.Adequacy.CanonReflectMutual.∨-false-l
d_'8744''45'false'45'l_12 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'false'45'l_12 = erased
-- Once.Adequacy.CanonReflectMutual.∨-false-r
d_'8744''45'false'45'r_18 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'false'45'r_18 = erased
-- Once.Adequacy.CanonReflectMutual.Names⊆
d_Names'8838'_22 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> ()
d_Names'8838'_22 = erased
-- Once.Adequacy.CanonReflectMutual.not-local
d_not'45'local_34 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_not'45'local_34 = erased
-- Once.Adequacy.CanonReflectMutual.¬unit-from-false
d_'172'unit'45'from'45'false_72 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'172'unit'45'from'45'false_72 = erased
-- Once.Adequacy.CanonReflectMutual.classifyRVar-applied-nonbuiltin
d_classifyRVar'45'applied'45'nonbuiltin_80 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyRVar'45'applied'45'nonbuiltin_80 = erased
-- Once.Adequacy.CanonReflectMutual.classifyRVar-nonbuiltin
d_classifyRVar'45'nonbuiltin_138 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyRVar'45'nonbuiltin_138 = erased
-- Once.Adequacy.CanonReflectMutual.classify-decanon-rvar
d_classify'45'decanon'45'rvar_284 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classify'45'decanon'45'rvar_284 = erased
-- Once.Adequacy.CanonReflectMutual.classify-decanon-bare-rvar
d_classify'45'decanon'45'bare'45'rvar_312 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classify'45'decanon'45'bare'45'rvar_312 = erased
-- Once.Adequacy.CanonReflectMutual.classify-decanon
d_classify'45'decanon_334 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classify'45'decanon_334 = erased
-- Once.Adequacy.CanonReflectMutual.composeMid-decanon
d_composeMid'45'decanon_632 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_composeMid'45'decanon_632 = erased
-- Once.Adequacy.CanonReflectMutual.reflect-gvar
d_reflect'45'gvar_662 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14
d_reflect'45'gvar_662 ~v0 ~v1 v2 ~v3 ~v4 v5
  = du_reflect'45'gvar_662 v2 v5
du_reflect'45'gvar_662 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14
du_reflect'45'gvar_662 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.Adequacy.CanonReflectMutual.reflect-neg-var-ᵍ
d_reflect'45'neg'45'var'45''7501'_684 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14
d_reflect'45'neg'45'var'45''7501'_684 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_reflect'45'neg'45'var'45''7501'_684
du_reflect'45'neg'45'var'45''7501'_684 ::
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14
du_reflect'45'neg'45'var'45''7501'_684
  = MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonReflectMutual.canon-reflects-ᵍ
d_canon'45'reflects'45''7501'_706 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14
d_canon'45'reflects'45''7501'_706 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v5
        -> coe
             du_reflect'45'gvar_662
             (coe
                MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                (coe
                   MAlonzo.Code.Once.Parser.Module.Resolve.d_elemStr_194 (coe v5)
                   (coe v2))
                (coe
                   MAlonzo.Code.Once.Parser.Module.Resolve.d_isBuiltinName_192
                   (coe v5)))
             (coe v4)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v5 v6
        -> case coe v5 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v7
               -> coe
                    du_reflect'45'gapp_720 (coe v0) (coe v1)
                    (coe
                       MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                       (coe
                          MAlonzo.Code.Once.Parser.Module.Resolve.d_elemStr_194 (coe v7)
                          (coe v2))
                       (coe
                          MAlonzo.Code.Once.Parser.Module.Resolve.d_isBuiltinName_192
                          (coe v7)))
                    (coe v2) (coe v6) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v5 v6
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'pair_418 v12 v13
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'42'__126 v14 v15
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'pair_418
                           (d_canon'45'reflects'45''7501'_706
                              (coe v0) (coe v14) (coe v2) (coe v5) (coe v12))
                           (d_canon'45'reflects'45''7501'_706
                              (coe v0) (coe v15) (coe v2) (coe v6) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v5 -> coe v4
      MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v5 v6 v7 v8 -> coe v4
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v6
        -> case coe v6 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v7
               -> coe du_reflect'45'neg'45'var'45''7501'_684
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v7
               -> case coe v4 of
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'neg'45'int_390
                      -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'neg'45'int_390
                    _ -> erased
             MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v7 v8 v9 v10
               -> case coe v4 of
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'neg'45'float_402
                      -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'neg'45'float_402
                    _ -> erased
             _ -> erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonReflectMutual.reflect-gapp
d_reflect'45'gapp_720 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14
d_reflect'45'gapp_720 v0 v1 v2 v3 ~v4 v5 v6
  = du_reflect'45'gapp_720 v0 v1 v2 v3 v5 v6
du_reflect'45'gapp_720 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14
du_reflect'45'gapp_720 v0 v1 v2 v3 v4 v5
  = coe
      seq (coe v2)
      (case coe v5 of
         MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inl_428 v10
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'43'__128 v11 v12
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inl_428
                       (d_canon'45'reflects'45''7501'_706
                          (coe v0) (coe v11) (coe v3) (coe v4) (coe v10))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inr_438 v10
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'43'__128 v11 v12
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inr_438
                       (d_canon'45'reflects'45''7501'_706
                          (coe v0) (coe v12) (coe v3) (coe v4) (coe v10))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'In_448 v9 v11
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_μ'45'type_132 v12
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'In_448 v9
                       (d_canon'45'reflects'45''7501'_706
                          (coe v0)
                          (coe
                             MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v12) (coe v1))
                          (coe v3) (coe v4) (coe v11))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.CanonReflectMutual.reflect-var-ᵢ
d_reflect'45'var'45''7522'_1116 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_reflect'45'var'45''7522'_1116 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflect'45'var'45''7522'_1116 v3 v8
du_reflect'45'var'45''7522'_1116 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_reflect'45'var'45''7522'_1116 v0 v1
  = if coe v0
      then coe v1
      else (case coe v1 of
              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_86 v6
                -> coe
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_94 v6
              _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.CanonReflectMutual.reflect-var-ᵐ
d_reflect'45'var'45''7504'_1156 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18
d_reflect'45'var'45''7504'_1156 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8
                                v9
  = du_reflect'45'var'45''7504'_1156 v4 v9
du_reflect'45'var'45''7504'_1156 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18
du_reflect'45'var'45''7504'_1156 v0 v1
  = if coe v0
      then coe v1
      else (case coe v1 of
              MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named'45'resolved_620 v8 v9
                -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named_608 v8 v9
              _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.CanonReflectMutual.reflect-var-ᶜ
d_reflect'45'var'45''7580'_1196 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
d_reflect'45'var'45''7580'_1196 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflect'45'var'45''7580'_1196 v1 v3 v8
du_reflect'45'var'45''7580'_1196 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
du_reflect'45'var'45''7580'_1196 v0 v1 v2
  = if coe v1
      then coe v2
      else (case coe v2 of
              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632 v8
                -> coe
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632
                     (coe du_reflect'45'var'45''7504'_1156 (coe v1) (coe v8))
              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_642 v7
                -> coe
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_642
                     (coe du_reflect'45'var'45''7522'_1116 (coe v1) (coe v7))
              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_758 v8
                -> case coe v0 of
                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v9 v10 v11
                       -> coe
                            MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_758
                            (coe
                               du_reflect'45'var'45''7580'_1196
                               (coe
                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v9)
                                  (coe
                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                                     (coe MAlonzo.Code.Once.Type.C_pure_34))
                                  (coe v11))
                               (coe v1) (coe v8))
                     _ -> MAlonzo.RTE.mazUnreachableError
              _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.CanonReflectMutual.reflect-neg-var-ᵢ
d_reflect'45'neg'45'var'45''7522'_1264 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_reflect'45'neg'45'var'45''7522'_1264 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 v7
                                       v8
  = du_reflect'45'neg'45'var'45''7522'_1264 v2 v3 v7 v8
du_reflect'45'neg'45'var'45''7522'_1264 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  Bool ->
  (MAlonzo.Code.Once.Type.T_Type_112 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_reflect'45'neg'45'var'45''7522'_1264 v0 v1 v2 v3
  = coe
      seq (coe v1)
      (case coe v3 of
         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_144 v7
           -> coe
                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_144
                (coe v2 (coe MAlonzo.Code.Once.Type.C_Int_136) v0 v7)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.CanonReflectMutual.canon-reflects-ᵢ
d_canon'45'reflects'45''7522'_1296 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_canon'45'reflects'45''7522'_1296 v0 v1 v2 v3 v4 ~v5 v6
  = du_canon'45'reflects'45''7522'_1296 v0 v1 v2 v3 v4 v6
du_canon'45'reflects'45''7522'_1296 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_canon'45'reflects'45''7522'_1296 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v6
        -> coe
             du_reflect'45'var'45''7522'_1116
             (coe
                MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                (coe
                   MAlonzo.Code.Once.Parser.Module.Resolve.d_elemStr_194 (coe v6)
                   (coe v3))
                (coe
                   MAlonzo.Code.Once.Parser.Module.Resolve.d_isBuiltinName_192
                   (coe v6)))
             (coe v5)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v6 v7 -> coe v5
      MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v6 -> coe v5
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v6 v7
        -> let v8
                 = case coe v5 of
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_350 v11 v13 v14 v15 v17 v18
                       -> coe
                            MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_350 v11 v13 v14 v15
                            (coe
                               du_canon'45'reflects'45''7522'_1296 (coe v0)
                               (coe
                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v11)
                                  (coe
                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v13)
                                     (coe MAlonzo.Code.Once.Type.C_pure_34))
                                  (coe v1))
                               (coe v14) (coe v3) (coe v6) (coe v17))
                            (coe
                               du_canon'45'reflects'45''7580'_1376 (coe v0) (coe v11) (coe v15)
                               (coe v3) (coe v7) (coe v18))
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_366 v11 v13 v14 v16 v17
                       -> case coe v1 of
                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v18 v19 v20
                              -> coe
                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_366 v11 v13
                                   v14
                                   (coe
                                      du_canon'45'reflects'45''7522'_1296 (coe v0)
                                      (coe
                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v11)
                                         (coe
                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                            (coe MAlonzo.Code.Once.Type.C_Many_10)
                                            (coe MAlonzo.Code.Once.Type.C_eff_36))
                                         (coe v20))
                                      (coe v13) (coe v3) (coe v6) (coe v16))
                                   (coe
                                      du_canon'45'reflects'45''7580'_1376 (coe v0) (coe v11)
                                      (coe v14) (coe v3) (coe v7) (coe v17))
                            _ -> MAlonzo.RTE.mazUnreachableError
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v6 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v9
                  -> coe
                       du_reflect'45'app'45'var'45''7522'_1312 (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                          (coe
                             MAlonzo.Code.Once.Parser.Module.Resolve.d_elemStr_194 (coe v9)
                             (coe v3))
                          (coe
                             MAlonzo.Code.Once.Parser.Module.Resolve.d_isBuiltinName_192
                             (coe v9)))
                       (coe v3) (coe v7) (coe v5)
                _ -> coe v8)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v6 v7 v8
        -> case coe v5 of
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_176 v13 v15 v16 v17 v18 v19
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_176 v13 v15 v16 v17
                    (coe
                       du_canon'45'reflects'45''7522'_1296 (coe v0) (coe v13) (coe v16)
                       (coe v3) (coe v7) (coe v18))
                    (coe
                       du_canon'45'reflects'45''7522'_1296
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402 (coe v0)
                          (coe v6) (coe v13))
                       (coe v1)
                       (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v15 v17)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v6) (coe v3))
                       (coe v8) (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v6 v7
        -> case coe v5 of
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_136 v13 v14 v15 v16
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'42'__126 v17 v18
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_136 v13 v14
                           (coe
                              du_canon'45'reflects'45''7522'_1296 (coe v0) (coe v17) (coe v13)
                              (coe v3) (coe v6) (coe v15))
                           (coe
                              du_canon'45'reflects'45''7522'_1296 (coe v0) (coe v18) (coe v14)
                              (coe v3) (coe v7) (coe v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v6 v7 v8 v9 v10
        -> case coe v5 of
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_206 v17 v18 v20 v21 v22 v23 v24 v25 v26 v27
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_206 v17 v18 v20
                    v21 v22 v23 v24
                    (coe
                       du_canon'45'reflects'45''7522'_1296 (coe v0)
                       (coe MAlonzo.Code.Once.Type.C__'43'__128 (coe v17) (coe v18))
                       (coe v22) (coe v3) (coe v6) (coe v25))
                    (coe
                       du_canon'45'reflects'45''7522'_1296
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402 (coe v0)
                          (coe v7) (coe v17))
                       (coe v1)
                       (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v20 v23)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v7) (coe v3))
                       (coe v8) (coe v26))
                    (coe
                       du_canon'45'reflects'45''7522'_1296
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402 (coe v0)
                          (coe v9) (coe v18))
                       (coe v1)
                       (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v21 v24)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v9) (coe v3))
                       (coe v10) (coe v27))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_52 -> coe v5
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v6 -> coe v5
      MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v6 v7 v8 v9 -> coe v5
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_58 v6 -> coe v5
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v6 v7
        -> case coe v5 of
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_120 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_120
                    (coe
                       du_canon'45'reflects'45''7580'_1376 (coe v0) (coe v7) (coe v2)
                       (coe v3) (coe v6) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v6 v7 v8
        -> case coe v5 of
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_220 v13 v14 v16 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_220 v13
                    v14
                    (coe
                       du_canon'45'reflects'45''7522'_1296 (coe v0)
                       (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v13) (coe v3) (coe v7)
                       (coe v16))
                    (coe
                       du_canon'45'reflects'45''7522'_1296 (coe v0)
                       (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v14) (coe v3) (coe v8)
                       (coe v17))
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_234 v13 v14 v16 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_234
                    v13 v14
                    (coe
                       du_canon'45'reflects'45''7522'_1296 (coe v0)
                       (coe MAlonzo.Code.Once.Type.C_Float_138) (coe v13) (coe v3)
                       (coe v7) (coe v16))
                    (coe
                       du_canon'45'reflects'45''7522'_1296 (coe v0)
                       (coe MAlonzo.Code.Once.Type.C_Float_138) (coe v14) (coe v3)
                       (coe v8) (coe v17))
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_248 v13 v14 v16 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_248
                    v13 v14
                    (coe
                       du_canon'45'reflects'45''7522'_1296 (coe v0)
                       (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v13) (coe v3) (coe v7)
                       (coe v16))
                    (coe
                       du_canon'45'reflects'45''7522'_1296 (coe v0)
                       (coe MAlonzo.Code.Once.Type.C_Float_138) (coe v14) (coe v3)
                       (coe v8) (coe v17))
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_262 v13 v14 v16 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_262
                    v13 v14
                    (coe
                       du_canon'45'reflects'45''7522'_1296 (coe v0)
                       (coe MAlonzo.Code.Once.Type.C_Float_138) (coe v13) (coe v3)
                       (coe v7) (coe v16))
                    (coe
                       du_canon'45'reflects'45''7522'_1296 (coe v0)
                       (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v14) (coe v3) (coe v8)
                       (coe v17))
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_276 v13 v14 v16 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_276 v13
                    v14
                    (coe
                       du_canon'45'reflects'45''7522'_1296 (coe v0)
                       (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v13) (coe v3) (coe v7)
                       (coe v16))
                    (coe
                       du_canon'45'reflects'45''7522'_1296 (coe v0)
                       (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v14) (coe v3) (coe v8)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v7
        -> let v8
                 = case coe v5 of
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_144 v11
                       -> coe
                            MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_144
                            (coe
                               du_canon'45'reflects'45''7522'_1296 (coe v0)
                               (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v2) (coe v3) (coe v7)
                               (coe v11))
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v7 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v9
                  -> coe
                       du_reflect'45'neg'45'var'45''7522'_1264 (coe v2)
                       (coe
                          MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                          (coe
                             MAlonzo.Code.Once.Parser.Module.Resolve.d_elemStr_194 (coe v9)
                             (coe v3))
                          (coe
                             MAlonzo.Code.Once.Parser.Module.Resolve.d_isBuiltinName_192
                             (coe v9)))
                       (coe
                          (\ v10 v11 ->
                             coe
                               du_canon'45'reflects'45''7522'_1296 (coe v0) (coe v10) (coe v11)
                               (coe v3) (coe v7)))
                       (coe v5)
                MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v9 v10 v11 v12
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_156
                         -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_156
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_144 v16
                         -> coe
                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_144
                              (coe
                                 du_canon'45'reflects'45''7522'_1296 (coe v0)
                                 (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v2) (coe v3) (coe v7)
                                 (coe v16))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonReflectMutual.reflect-app-var-ᵢ
d_reflect'45'app'45'var'45''7522'_1312 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_reflect'45'app'45'var'45''7522'_1312 v0 v1 ~v2 v3 v4 ~v5 v6 ~v7
                                       ~v8 v9
  = du_reflect'45'app'45'var'45''7522'_1312 v0 v1 v3 v4 v6 v9
du_reflect'45'app'45'var'45''7522'_1312 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_reflect'45'app'45'var'45''7522'_1312 v0 v1 v2 v3 v4 v5
  = if coe v2
      then case coe v5 of
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_286 v9 v10
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_286 v9
                    (coe
                       du_canon'45'reflects'45''7522'_1296 (coe v0) (coe v1) (coe v9)
                       (coe v3) (coe v4) (coe v10))
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_298 v9 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_298 v9 v10
                    (coe
                       du_canon'45'reflects'45''7522'_1296 (coe v0)
                       (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v1) (coe v9))
                       (coe v10) (coe v3) (coe v4) (coe v11))
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_310 v8 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_310 v8 v10
                    (coe
                       du_canon'45'reflects'45''7522'_1296 (coe v0)
                       (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v8) (coe v1))
                       (coe v10) (coe v3) (coe v4) (coe v11))
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_320 v8 v9 v10
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_320 v8
                    v9
                    (coe
                       du_canon'45'reflects'45''7522'_1296 (coe v0) (coe v8) (coe v9)
                       (coe v3) (coe v4) (coe v10))
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_332 v8 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_332
                    v8 v10
                    (coe
                       du_canon'45'reflects'45''7522'_1296 (coe v0)
                       (coe
                          MAlonzo.Code.Once.Type.C__'42'__126
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v8)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe v1))
                          (coe v8))
                       (coe v10) (coe v3) (coe v4) (coe v11))
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_350 v9 v11 v12 v13 v15 v16
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_350 v9 v11 v12 v13
                    v15
                    (coe
                       du_canon'45'reflects'45''7580'_1376 (coe v0) (coe v9) (coe v13)
                       (coe v3) (coe v4) (coe v16))
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_366 v9 v11 v12 v14 v15
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_366 v9 v11 v12
                    v14
                    (coe
                       du_canon'45'reflects'45''7580'_1376 (coe v0) (coe v9) (coe v12)
                       (coe v3) (coe v4) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      else (case coe v5 of
              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_350 v9 v11 v12 v13 v15 v16
                -> coe
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_350 v9 v11 v12 v13
                     (coe du_reflect'45'var'45''7522'_1116 (coe v2) (coe v15))
                     (coe
                        du_canon'45'reflects'45''7580'_1376 (coe v0) (coe v9) (coe v13)
                        (coe v3) (coe v4) (coe v16))
              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_366 v9 v11 v12 v14 v15
                -> coe
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_366 v9 v11 v12
                     (coe du_reflect'45'var'45''7522'_1116 (coe v2) (coe v14))
                     (coe
                        du_canon'45'reflects'45''7580'_1376 (coe v0) (coe v9) (coe v12)
                        (coe v3) (coe v4) (coe v15))
              _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.CanonReflectMutual.canon-reflects-ᵐ
d_canon'45'reflects'45''7504'_1326 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18
d_canon'45'reflects'45''7504'_1326 v0 v1 v2 v3 v4 v5 ~v6 v7
  = du_canon'45'reflects'45''7504'_1326 v0 v1 v2 v3 v4 v5 v7
du_canon'45'reflects'45''7504'_1326 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18
du_canon'45'reflects'45''7504'_1326 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = case coe v6 of
              MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_596 v12
                -> coe
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_596
                     (d_canon'45'reflects'45''7501'_706
                        (coe v0) (coe v3) (coe v4) (coe v5) (coe v12))
              _ -> MAlonzo.RTE.mazUnreachableError in
    coe
      (case coe v5 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v8
           -> coe
                du_reflect'45'var'45''7504'_1156
                (coe
                   MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                   (coe
                      MAlonzo.Code.Once.Parser.Module.Resolve.d_elemStr_194 (coe v8)
                      (coe v4))
                   (coe
                      MAlonzo.Code.Once.Parser.Module.Resolve.d_isBuiltinName_192
                      (coe v8)))
                (coe v6)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v8
           -> case coe v6 of
                MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named'45'resolved_620 v15 v16
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named'45'resolved_620
                       v15 v16
                MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_596 v14
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_596
                       (d_canon'45'reflects'45''7501'_706
                          (coe v0) (coe v3) (coe v4) (coe v5) (coe v14))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v8 v9
           -> case coe v8 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v10
                  -> coe
                       du_reflect'45'app'45'var'45''7504'_1344 (coe v0) (coe v1) (coe v2)
                       (coe v3)
                       (coe
                          MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                          (coe
                             MAlonzo.Code.Once.Parser.Module.Resolve.d_elemStr_194 (coe v10)
                             (coe v4))
                          (coe
                             MAlonzo.Code.Once.Parser.Module.Resolve.d_isBuiltinName_192
                             (coe v10)))
                       (coe v4) (coe v9) (coe v6)
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
                  -> case coe v10 of
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v12
                         -> coe
                              du_reflect'45'app2'45'var'45''7504'_1364 (coe v0) (coe v1) (coe v2)
                              (coe v3)
                              (coe
                                 MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                                 (coe
                                    MAlonzo.Code.Once.Parser.Module.Resolve.d_elemStr_194 (coe v12)
                                    (coe v4))
                                 (coe
                                    MAlonzo.Code.Once.Parser.Module.Resolve.d_isBuiltinName_192
                                    (coe v12)))
                              (coe v4) (coe v11) (coe v9) (coe v6)
                       _ -> coe v7
                _ -> coe v7
         _ -> coe v7)
-- Once.Adequacy.CanonReflectMutual.reflect-app-var-ᵐ
d_reflect'45'app'45'var'45''7504'_1344 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18
d_reflect'45'app'45'var'45''7504'_1344 v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8
                                       ~v9 v10
  = du_reflect'45'app'45'var'45''7504'_1344 v0 v1 v2 v3 v4 v5 v7 v10
du_reflect'45'app'45'var'45''7504'_1344 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18
du_reflect'45'app'45'var'45''7504'_1344 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      seq (coe v4)
      (case coe v7 of
         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'curry_570 v13
           -> case coe v3 of
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v14 v15 v16
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'curry_570
                       (coe
                          du_canon'45'reflects'45''7504'_1326 (coe v0)
                          (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v1) (coe v14))
                          (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v16) (coe v5) (coe v6)
                          (coe v13))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'cata_584 v13 v15
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_μ'45'type_132 v16
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'cata_584 v13
                       (coe
                          du_canon'45'reflects'45''7504'_1326
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                             (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364 (coe v0)))
                          (coe
                             MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v16) (coe v3))
                          (coe v2) (coe v3) (coe v5) (coe v6) (coe v15))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_596 v13
           -> coe
                MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_596
                (coe
                   du_reflect'45'gapp_720 (coe v0) (coe v3)
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) (coe v5) (coe v6)
                   (coe v13))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.CanonReflectMutual.reflect-app2-var-ᵐ
d_reflect'45'app2'45'var'45''7504'_1364 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18
d_reflect'45'app2'45'var'45''7504'_1364 v0 v1 v2 v3 v4 v5 ~v6 v7 v8
                                        ~v9 ~v10 v11
  = du_reflect'45'app2'45'var'45''7504'_1364
      v0 v1 v2 v3 v4 v5 v7 v8 v11
du_reflect'45'app2'45'var'45''7504'_1364 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18
du_reflect'45'app2'45'var'45''7504'_1364 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      seq (coe v4)
      (case coe v8 of
         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'compose_528 v13 v17 v18
           -> coe
                MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'compose_528 v13
                (coe
                   du_canon'45'reflects'45''7504'_1326 (coe v0) (coe v13) (coe v2)
                   (coe v3) (coe v5) (coe v6) (coe v17))
                (coe
                   du_canon'45'reflects'45''7504'_1326 (coe v0) (coe v1) (coe v2)
                   (coe v13) (coe v5) (coe v7) (coe v18))
         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'case_544 v16 v17
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'43'__128 v18 v19
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'case_544
                       (coe
                          du_canon'45'reflects'45''7504'_1326 (coe v0) (coe v18) (coe v2)
                          (coe v3) (coe v5) (coe v6) (coe v16))
                       (coe
                          du_canon'45'reflects'45''7504'_1326 (coe v0) (coe v19) (coe v2)
                          (coe v3) (coe v5) (coe v7) (coe v17))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'pair_558 v15 v16
           -> case coe v3 of
                MAlonzo.Code.Once.Type.C__'42'__126 v17 v18
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'pair_558
                       (coe
                          du_canon'45'reflects'45''7504'_1326 (coe v0) (coe v1)
                          (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v17) (coe v5) (coe v6)
                          (coe v15))
                       (coe
                          du_canon'45'reflects'45''7504'_1326 (coe v0) (coe v1)
                          (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v18) (coe v5) (coe v7)
                          (coe v16))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.CanonReflectMutual.canon-reflects-ᶜ
d_canon'45'reflects'45''7580'_1376 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
d_canon'45'reflects'45''7580'_1376 v0 v1 v2 v3 v4 ~v5 v6
  = du_canon'45'reflects'45''7580'_1376 v0 v1 v2 v3 v4 v6
du_canon'45'reflects'45''7580'_1376 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
du_canon'45'reflects'45''7580'_1376 v0 v1 v2 v3 v4 v5
  = let v6
          = case coe v5 of
              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632 v11
                -> case coe v1 of
                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v12 v13 v14
                       -> case coe v13 of
                            MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                              -> coe
                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632
                                   (coe
                                      du_canon'45'reflects'45''7504'_1326 (coe v0) (coe v12)
                                      (coe v16) (coe v14) (coe v3) (coe v4) (coe v11))
                            _ -> MAlonzo.RTE.mazUnreachableError
                     _ -> MAlonzo.RTE.mazUnreachableError
              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_642 v10
                -> coe
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_642
                     (coe
                        du_canon'45'reflects'45''7522'_1296 (coe v0) (coe v1) (coe v2)
                        (coe v3) (coe v4) (coe v10))
              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672 v11
                -> case coe v1 of
                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v12 v13 v14
                       -> coe
                            MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672
                            (d_canon'45'reflects'45''7501'_706
                               (coe v0) (coe v14) (coe v3) (coe v4) (coe v11))
                     _ -> MAlonzo.RTE.mazUnreachableError
              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_758 v11
                -> case coe v1 of
                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v12 v13 v14
                       -> coe
                            MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_758
                            (coe
                               du_canon'45'reflects'45''7580'_1376 (coe v0)
                               (coe
                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v12)
                                  (coe
                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                                     (coe MAlonzo.Code.Once.Type.C_pure_34))
                                  (coe v14))
                               (coe v2) (coe v3) (coe v4) (coe v11))
                     _ -> MAlonzo.RTE.mazUnreachableError
              _ -> MAlonzo.RTE.mazUnreachableError in
    coe
      (case coe v4 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v7
           -> coe
                du_reflect'45'var'45''7580'_1196 (coe v1)
                (coe
                   MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                   (coe
                      MAlonzo.Code.Once.Parser.Module.Resolve.d_elemStr_194 (coe v7)
                      (coe v3))
                   (coe
                      MAlonzo.Code.Once.Parser.Module.Resolve.d_isBuiltinName_192
                      (coe v7)))
                (coe v5)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v7 v8
           -> let v9
                    = case coe v5 of
                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_774 v12 v14 v15 v17 v18
                          -> coe
                               MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_774
                               v12 v14 v15
                               (coe
                                  du_canon'45'reflects'45''7522'_1296 (coe v0) (coe v12) (coe v15)
                                  (coe v3) (coe v8) (coe v17))
                               (coe
                                  du_canon'45'reflects'45''7580'_1376 (coe v0)
                                  (coe
                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v12)
                                     (coe
                                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                                        (coe MAlonzo.Code.Once.Type.C_pure_34))
                                     (coe v1))
                                  (coe v14) (coe v3) (coe v7) (coe v18))
                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632 v14
                          -> case coe v1 of
                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v15 v16 v17
                                 -> case coe v16 of
                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50 v18 v19
                                        -> coe
                                             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632
                                             (coe
                                                du_canon'45'reflects'45''7504'_1326 (coe v0)
                                                (coe v15) (coe v19) (coe v17) (coe v3) (coe v4)
                                                (coe v14))
                                      _ -> MAlonzo.RTE.mazUnreachableError
                               _ -> MAlonzo.RTE.mazUnreachableError
                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_642 v13
                          -> coe
                               MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_642
                               (coe
                                  du_canon'45'reflects'45''7522'_1296 (coe v0) (coe v1) (coe v2)
                                  (coe v3) (coe v4) (coe v13))
                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672 v14
                          -> case coe v1 of
                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v15 v16 v17
                                 -> coe
                                      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672
                                      (d_canon'45'reflects'45''7501'_706
                                         (coe v0) (coe v17) (coe v3) (coe v4) (coe v14))
                               _ -> MAlonzo.RTE.mazUnreachableError
                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_758 v14
                          -> case coe v1 of
                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v15 v16 v17
                                 -> coe
                                      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_758
                                      (coe
                                         du_canon'45'reflects'45''7580'_1376 (coe v0)
                                         (coe
                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v15)
                                            (coe
                                               MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                               (coe MAlonzo.Code.Once.Type.C_Many_10)
                                               (coe MAlonzo.Code.Once.Type.C_pure_34))
                                            (coe v17))
                                         (coe v2) (coe v3) (coe v4) (coe v14))
                               _ -> MAlonzo.RTE.mazUnreachableError
                        _ -> MAlonzo.RTE.mazUnreachableError in
              coe
                (case coe v7 of
                   MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v10
                     -> coe
                          du_reflect'45'app'45'var'45''7580'_1392 (coe v0) (coe v1)
                          (coe
                             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                             (coe
                                MAlonzo.Code.Once.Parser.Module.Resolve.d_elemStr_194 (coe v10)
                                (coe v3))
                             (coe
                                MAlonzo.Code.Once.Parser.Module.Resolve.d_isBuiltinName_192
                                (coe v10)))
                          (coe v3) (coe v8) (coe v5)
                   _ -> coe v9)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v7 v8
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_660 v15 v18
                  -> case coe v1 of
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v19 v20 v21
                         -> coe
                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_660 v15
                              (coe
                                 du_canon'45'reflects'45''7580'_1376
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402
                                    (coe v0) (coe v7) (coe v19))
                                 (coe v21)
                                 (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v15 v2)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v7) (coe v3))
                                 (coe v8) (coe v18))
                       _ -> coe v6
                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632 v14
                  -> case coe v1 of
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v15 v16 v17
                         -> case coe v16 of
                              MAlonzo.Code.Once.Type.C_mk'45'kind_50 v18 v19
                                -> coe
                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632
                                     (coe
                                        du_canon'45'reflects'45''7504'_1326 (coe v0) (coe v15)
                                        (coe v19) (coe v17) (coe v3) (coe v4) (coe v14))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_642 v13
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_642
                       (coe
                          du_canon'45'reflects'45''7522'_1296 (coe v0) (coe v1) (coe v2)
                          (coe v3) (coe v4) (coe v13))
                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672 v14
                  -> case coe v1 of
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v15 v16 v17
                         -> coe
                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672
                              (d_canon'45'reflects'45''7501'_706
                                 (coe v0) (coe v17) (coe v3) (coe v4) (coe v14))
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_758 v14
                  -> case coe v1 of
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v15 v16 v17
                         -> coe
                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_758
                              (coe
                                 du_canon'45'reflects'45''7580'_1376 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v15)
                                    (coe
                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                       (coe MAlonzo.Code.Once.Type.C_Many_10)
                                       (coe MAlonzo.Code.Once.Type.C_pure_34))
                                    (coe v17))
                                 (coe v2) (coe v3) (coe v4) (coe v14))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v7 v8
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_688 v14 v15 v16 v17
                  -> case coe v1 of
                       MAlonzo.Code.Once.Type.C__'42'__126 v18 v19
                         -> coe
                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_688
                              v14 v15
                              (coe
                                 du_canon'45'reflects'45''7580'_1376 (coe v0) (coe v18) (coe v14)
                                 (coe v3) (coe v7) (coe v16))
                              (coe
                                 du_canon'45'reflects'45''7580'_1376 (coe v0) (coe v19) (coe v15)
                                 (coe v3) (coe v8) (coe v17))
                       _ -> coe v6
                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632 v14
                  -> case coe v1 of
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v15 v16 v17
                         -> case coe v16 of
                              MAlonzo.Code.Once.Type.C_mk'45'kind_50 v18 v19
                                -> coe
                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632
                                     (coe
                                        du_canon'45'reflects'45''7504'_1326 (coe v0) (coe v15)
                                        (coe v19) (coe v17) (coe v3) (coe v4) (coe v14))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_642 v13
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_642
                       (coe
                          du_canon'45'reflects'45''7522'_1296 (coe v0) (coe v1) (coe v2)
                          (coe v3) (coe v4) (coe v13))
                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672 v14
                  -> case coe v1 of
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v15 v16 v17
                         -> coe
                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672
                              (d_canon'45'reflects'45''7501'_706
                                 (coe v0) (coe v17) (coe v3) (coe v4) (coe v14))
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_758 v14
                  -> case coe v1 of
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v15 v16 v17
                         -> coe
                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_758
                              (coe
                                 du_canon'45'reflects'45''7580'_1376 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v15)
                                    (coe
                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                       (coe MAlonzo.Code.Once.Type.C_Many_10)
                                       (coe MAlonzo.Code.Once.Type.C_pure_34))
                                    (coe v17))
                                 (coe v2) (coe v3) (coe v4) (coe v14))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v6)
-- Once.Adequacy.CanonReflectMutual.reflect-app-var-ᶜ
d_reflect'45'app'45'var'45''7580'_1392 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
d_reflect'45'app'45'var'45''7580'_1392 v0 v1 ~v2 v3 v4 ~v5 v6 ~v7
                                       ~v8 v9
  = du_reflect'45'app'45'var'45''7580'_1392 v0 v1 v3 v4 v6 v9
du_reflect'45'app'45'var'45''7580'_1392 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24
du_reflect'45'app'45'var'45''7580'_1392 v0 v1 v2 v3 v4 v5
  = if coe v2
      then case coe v5 of
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v12 v13 v14
                      -> case coe v13 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                             -> coe
                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632
                                  (coe
                                     du_reflect'45'app'45'var'45''7504'_1344 (coe v0) (coe v12)
                                     (coe v16) (coe v14) (coe v2) (coe v3) (coe v4) (coe v11))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_642 v10
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_642
                    (coe
                       du_reflect'45'app'45'var'45''7522'_1312 (coe v0) (coe v1) (coe v2)
                       (coe v3) (coe v4) (coe v10))
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v12 v13 v14
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672
                           (coe
                              du_reflect'45'gapp_720 (coe v0) (coe v14) (coe v2) (coe v3)
                              (coe v4) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_700 v9 v10 v12
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_132 v13
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_700
                           v9 v10
                           (coe
                              du_canon'45'reflects'45''7580'_1376 (coe v0)
                              (coe
                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v13) (coe v1))
                              (coe v10) (coe v3) (coe v4) (coe v12))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_712 v8 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_712 v8
                    v10
                    (coe
                       du_canon'45'reflects'45''7522'_1296 (coe v0)
                       (coe
                          MAlonzo.Code.Once.Type.C__'42'__126
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v8)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe v1))
                          (coe v8))
                       (coe v10) (coe v3) (coe v4) (coe v11))
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_724 v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v12 v13
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_724
                           v10
                           (coe
                              du_canon'45'reflects'45''7580'_1376 (coe v0) (coe v12) (coe v10)
                              (coe v3) (coe v4) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_736 v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v12 v13
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_736
                           v10
                           (coe
                              du_canon'45'reflects'45''7580'_1376 (coe v0) (coe v13) (coe v10)
                              (coe v3) (coe v4) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_746 v9 v10
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_746
                    v9
                    (coe
                       du_canon'45'reflects'45''7580'_1376 (coe v0)
                       (coe MAlonzo.Code.Once.Type.C_Void_124) (coe v9) (coe v3) (coe v4)
                       (coe v10))
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_758 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v12 v13 v14
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_758
                           (coe
                              du_reflect'45'app'45'var'45''7580'_1392 (coe v0)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v12)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe MAlonzo.Code.Once.Type.C_pure_34))
                                 (coe v14))
                              (coe v2) (coe v3) (coe v4) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_774 v9 v11 v12 v14 v15
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_774
                    v9 v11 v12
                    (coe
                       du_canon'45'reflects'45''7522'_1296 (coe v0) (coe v9) (coe v12)
                       (coe v3) (coe v4) (coe v14))
                    v15
             _ -> MAlonzo.RTE.mazUnreachableError
      else (case coe v5 of
              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632 v11
                -> case coe v1 of
                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v12 v13 v14
                       -> case coe v13 of
                            MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                              -> coe
                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632
                                   (coe
                                      du_reflect'45'app'45'var'45''7504'_1344 (coe v0) (coe v12)
                                      (coe v16) (coe v14) (coe v2) (coe v3) (coe v4) (coe v11))
                            _ -> MAlonzo.RTE.mazUnreachableError
                     _ -> MAlonzo.RTE.mazUnreachableError
              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_642 v10
                -> coe
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_642
                     (coe
                        du_reflect'45'app'45'var'45''7522'_1312 (coe v0) (coe v1) (coe v2)
                        (coe v3) (coe v4) (coe v10))
              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_758 v11
                -> case coe v1 of
                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v12 v13 v14
                       -> coe
                            MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_758
                            (coe
                               du_reflect'45'app'45'var'45''7580'_1392 (coe v0)
                               (coe
                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v12)
                                  (coe
                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                                     (coe MAlonzo.Code.Once.Type.C_pure_34))
                                  (coe v14))
                               (coe v2) (coe v3) (coe v4) (coe v11))
                     _ -> MAlonzo.RTE.mazUnreachableError
              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_774 v9 v11 v12 v14 v15
                -> coe
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_774
                     v9 v11 v12
                     (coe
                        du_canon'45'reflects'45''7522'_1296 (coe v0) (coe v9) (coe v12)
                        (coe v3) (coe v4) (coe v14))
                     (coe
                        du_reflect'45'var'45''7580'_1196
                        (coe
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v9)
                           (coe
                              MAlonzo.Code.Once.Type.C_mk'45'kind_50
                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                              (coe MAlonzo.Code.Once.Type.C_pure_34))
                           (coe v1))
                        (coe v2) (coe v15))
              _ -> MAlonzo.RTE.mazUnreachableError)
