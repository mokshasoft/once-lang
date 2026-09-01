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
-- Once.Adequacy.CanonReflectMutual.decanon-cls-app2
d_decanon'45'cls'45'app2_624 ::
  Bool ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_decanon'45'cls'45'app2_624 = erased
-- Once.Adequacy.CanonReflectMutual.composeMid-decanon
d_composeMid'45'decanon_650 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_composeMid'45'decanon_650 = erased
-- Once.Adequacy.CanonReflectMutual.reflect-var-ᵢ
d_reflect'45'var'45''7522'_684 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
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
d_reflect'45'var'45''7522'_684 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflect'45'var'45''7522'_684 v3 v8
du_reflect'45'var'45''7522'_684 ::
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_reflect'45'var'45''7522'_684 v0 v1
  = if coe v0
      then coe v1
      else (case coe v1 of
              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_78 v6
                -> coe
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_86 v6
              _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.CanonReflectMutual.reflect-var-ᶜ
d_reflect'45'var'45''7580'_722 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
d_reflect'45'var'45''7580'_722 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflect'45'var'45''7580'_722 v1 v3 v8
du_reflect'45'var'45''7580'_722 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Bool ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
du_reflect'45'var'45''7580'_722 v0 v1 v2
  = if coe v1
      then coe v2
      else (case coe v2 of
              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_518 v7
                -> coe
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_518
                     (coe du_reflect'45'var'45''7522'_684 (coe v1) (coe v7))
              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_622 v8
                -> case coe v0 of
                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v9 v10 v11
                       -> coe
                            MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_622
                            (coe
                               du_reflect'45'var'45''7580'_722
                               (coe
                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v9)
                                  (coe
                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                                     (coe MAlonzo.Code.Once.Type.C_pure_34))
                                  (coe v11))
                               (coe v1) (coe v8))
                     _ -> MAlonzo.RTE.mazUnreachableError
              _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.CanonReflectMutual.reflect-neg-var-ᵢ
d_reflect'45'neg'45'var'45''7522'_772 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_reflect'45'neg'45'var'45''7522'_772 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 v7
                                      v8
  = du_reflect'45'neg'45'var'45''7522'_772 v2 v3 v7 v8
du_reflect'45'neg'45'var'45''7522'_772 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  Bool ->
  (MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
   MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10) ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_reflect'45'neg'45'var'45''7522'_772 v0 v1 v2 v3
  = coe
      seq (coe v1)
      (case coe v3 of
         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_136 v7
           -> coe
                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_136
                (coe v2 (coe MAlonzo.Code.Once.Type.C_Int_132) v0 v7)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.CanonReflectMutual.canon-reflects-ᵢ
d_canon'45'reflects'45''7522'_804 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_canon'45'reflects'45''7522'_804 v0 v1 v2 v3 v4 ~v5 v6
  = du_canon'45'reflects'45''7522'_804 v0 v1 v2 v3 v4 v6
du_canon'45'reflects'45''7522'_804 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_canon'45'reflects'45''7522'_804 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v6
        -> coe
             du_reflect'45'var'45''7522'_684
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
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_342 v11 v13 v14 v15 v17 v18
                       -> coe
                            MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_342 v11 v13 v14 v15
                            (coe
                               du_canon'45'reflects'45''7522'_804 (coe v0)
                               (coe
                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v11)
                                  (coe
                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v13)
                                     (coe MAlonzo.Code.Once.Type.C_pure_34))
                                  (coe v1))
                               (coe v14) (coe v3) (coe v6) (coe v17))
                            (coe
                               du_canon'45'reflects'45''7580'_832 (coe v0) (coe v11) (coe v15)
                               (coe v3) (coe v7) (coe v18))
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_358 v11 v13 v14 v16 v17
                       -> case coe v1 of
                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v18 v19 v20
                              -> coe
                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_358 v11 v13
                                   v14
                                   (coe
                                      du_canon'45'reflects'45''7522'_804 (coe v0)
                                      (coe
                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v11)
                                         (coe
                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                            (coe MAlonzo.Code.Once.Type.C_Many_10)
                                            (coe MAlonzo.Code.Once.Type.C_eff_36))
                                         (coe v20))
                                      (coe v13) (coe v3) (coe v6) (coe v16))
                                   (coe
                                      du_canon'45'reflects'45''7580'_832 (coe v0) (coe v11)
                                      (coe v14) (coe v3) (coe v7) (coe v17))
                            _ -> MAlonzo.RTE.mazUnreachableError
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v6 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v9
                  -> coe
                       du_reflect'45'app'45'var'45''7522'_820 (coe v0) (coe v1)
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
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_168 v13 v15 v16 v17 v18 v19
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_168 v13 v15 v16 v17
                    (coe
                       du_canon'45'reflects'45''7522'_804 (coe v0) (coe v13) (coe v16)
                       (coe v3) (coe v7) (coe v18))
                    (coe
                       du_canon'45'reflects'45''7522'_804
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
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_128 v13 v14 v15 v16
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'42'__122 v17 v18
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_128 v13 v14
                           (coe
                              du_canon'45'reflects'45''7522'_804 (coe v0) (coe v17) (coe v13)
                              (coe v3) (coe v6) (coe v15))
                           (coe
                              du_canon'45'reflects'45''7522'_804 (coe v0) (coe v18) (coe v14)
                              (coe v3) (coe v7) (coe v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v6 v7 v8 v9 v10
        -> case coe v5 of
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_198 v17 v18 v20 v21 v22 v23 v24 v25 v26 v27
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_198 v17 v18 v20
                    v21 v22 v23 v24
                    (coe
                       du_canon'45'reflects'45''7522'_804 (coe v0)
                       (coe MAlonzo.Code.Once.Type.C__'43'__124 (coe v17) (coe v18))
                       (coe v22) (coe v3) (coe v6) (coe v25))
                    (coe
                       du_canon'45'reflects'45''7522'_804
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402 (coe v0)
                          (coe v7) (coe v17))
                       (coe v1)
                       (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v20 v23)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v7) (coe v3))
                       (coe v8) (coe v26))
                    (coe
                       du_canon'45'reflects'45''7522'_804
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
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_112 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_112
                    (coe
                       du_canon'45'reflects'45''7580'_832 (coe v0) (coe v7) (coe v2)
                       (coe v3) (coe v6) (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v6 v7 v8
        -> case coe v5 of
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_212 v13 v14 v16 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_212 v13
                    v14
                    (coe
                       du_canon'45'reflects'45''7522'_804 (coe v0)
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v13) (coe v3) (coe v7)
                       (coe v16))
                    (coe
                       du_canon'45'reflects'45''7522'_804 (coe v0)
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v14) (coe v3) (coe v8)
                       (coe v17))
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_226 v13 v14 v16 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_226
                    v13 v14
                    (coe
                       du_canon'45'reflects'45''7522'_804 (coe v0)
                       (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v13) (coe v3)
                       (coe v7) (coe v16))
                    (coe
                       du_canon'45'reflects'45''7522'_804 (coe v0)
                       (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v14) (coe v3)
                       (coe v8) (coe v17))
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_240 v13 v14 v16 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_240
                    v13 v14
                    (coe
                       du_canon'45'reflects'45''7522'_804 (coe v0)
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v13) (coe v3) (coe v7)
                       (coe v16))
                    (coe
                       du_canon'45'reflects'45''7522'_804 (coe v0)
                       (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v14) (coe v3)
                       (coe v8) (coe v17))
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_254 v13 v14 v16 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_254
                    v13 v14
                    (coe
                       du_canon'45'reflects'45''7522'_804 (coe v0)
                       (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v13) (coe v3)
                       (coe v7) (coe v16))
                    (coe
                       du_canon'45'reflects'45''7522'_804 (coe v0)
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v14) (coe v3) (coe v8)
                       (coe v17))
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_268 v13 v14 v16 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_268 v13
                    v14
                    (coe
                       du_canon'45'reflects'45''7522'_804 (coe v0)
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v13) (coe v3) (coe v7)
                       (coe v16))
                    (coe
                       du_canon'45'reflects'45''7522'_804 (coe v0)
                       (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v14) (coe v3) (coe v8)
                       (coe v17))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v7
        -> let v8
                 = case coe v5 of
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_136 v11
                       -> coe
                            MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_136
                            (coe
                               du_canon'45'reflects'45''7522'_804 (coe v0)
                               (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v2) (coe v3) (coe v7)
                               (coe v11))
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v7 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v9
                  -> coe
                       du_reflect'45'neg'45'var'45''7522'_772 (coe v2)
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
                               du_canon'45'reflects'45''7522'_804 (coe v0) (coe v10) (coe v11)
                               (coe v3) (coe v7)))
                       (coe v5)
                MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v9 v10 v11 v12
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_148
                         -> coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_148
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_136 v16
                         -> coe
                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_136
                              (coe
                                 du_canon'45'reflects'45''7522'_804 (coe v0)
                                 (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v2) (coe v3) (coe v7)
                                 (coe v16))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonReflectMutual.reflect-app-var-ᵢ
d_reflect'45'app'45'var'45''7522'_820 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
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
d_reflect'45'app'45'var'45''7522'_820 v0 v1 ~v2 v3 v4 ~v5 v6 ~v7
                                      ~v8 v9
  = du_reflect'45'app'45'var'45''7522'_820 v0 v1 v3 v4 v6 v9
du_reflect'45'app'45'var'45''7522'_820 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_reflect'45'app'45'var'45''7522'_820 v0 v1 v2 v3 v4 v5
  = if coe v2
      then case coe v5 of
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_278 v9 v10
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_278 v9
                    (coe
                       du_canon'45'reflects'45''7522'_804 (coe v0) (coe v1) (coe v9)
                       (coe v3) (coe v4) (coe v10))
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_290 v9 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_290 v9 v10
                    (coe
                       du_canon'45'reflects'45''7522'_804 (coe v0)
                       (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v1) (coe v9))
                       (coe v10) (coe v3) (coe v4) (coe v11))
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_302 v8 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_302 v8 v10
                    (coe
                       du_canon'45'reflects'45''7522'_804 (coe v0)
                       (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v8) (coe v1))
                       (coe v10) (coe v3) (coe v4) (coe v11))
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_312 v8 v9 v10
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_312 v8
                    v9
                    (coe
                       du_canon'45'reflects'45''7522'_804 (coe v0) (coe v8) (coe v9)
                       (coe v3) (coe v4) (coe v10))
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_324 v8 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_324
                    v8 v10
                    (coe
                       du_canon'45'reflects'45''7522'_804 (coe v0)
                       (coe
                          MAlonzo.Code.Once.Type.C__'42'__122
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v8)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe v1))
                          (coe v8))
                       (coe v10) (coe v3) (coe v4) (coe v11))
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_342 v9 v11 v12 v13 v15 v16
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_342 v9 v11 v12 v13
                    v15
                    (coe
                       du_canon'45'reflects'45''7580'_832 (coe v0) (coe v9) (coe v13)
                       (coe v3) (coe v4) (coe v16))
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_358 v9 v11 v12 v14 v15
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_358 v9 v11 v12
                    v14
                    (coe
                       du_canon'45'reflects'45''7580'_832 (coe v0) (coe v9) (coe v12)
                       (coe v3) (coe v4) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      else (case coe v5 of
              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_342 v9 v11 v12 v13 v15 v16
                -> coe
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_342 v9 v11 v12 v13
                     (coe du_reflect'45'var'45''7522'_684 (coe v2) (coe v15))
                     (coe
                        du_canon'45'reflects'45''7580'_832 (coe v0) (coe v9) (coe v13)
                        (coe v3) (coe v4) (coe v16))
              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_358 v9 v11 v12 v14 v15
                -> coe
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_358 v9 v11 v12
                     (coe du_reflect'45'var'45''7522'_684 (coe v2) (coe v14))
                     (coe
                        du_canon'45'reflects'45''7580'_832 (coe v0) (coe v9) (coe v12)
                        (coe v3) (coe v4) (coe v15))
              _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.CanonReflectMutual.canon-reflects-ᶜ
d_canon'45'reflects'45''7580'_832 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
d_canon'45'reflects'45''7580'_832 v0 v1 v2 v3 v4 ~v5 v6
  = du_canon'45'reflects'45''7580'_832 v0 v1 v2 v3 v4 v6
du_canon'45'reflects'45''7580'_832 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
du_canon'45'reflects'45''7580'_832 v0 v1 v2 v3 v4 v5
  = let v6
          = case coe v5 of
              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_518 v10
                -> coe
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_518
                     (coe
                        du_canon'45'reflects'45''7522'_804 (coe v0) (coe v1) (coe v2)
                        (coe v3) (coe v4) (coe v10))
              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_622 v11
                -> case coe v1 of
                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
                       -> coe
                            MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_622
                            (coe
                               du_canon'45'reflects'45''7580'_832 (coe v0)
                               (coe
                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v12)
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
                du_reflect'45'var'45''7580'_722 (coe v1)
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
                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_638 v12 v14 v15 v17 v18
                          -> coe
                               MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_638
                               v12 v14 v15
                               (coe
                                  du_canon'45'reflects'45''7522'_804 (coe v0) (coe v12) (coe v15)
                                  (coe v3) (coe v8) (coe v17))
                               (coe
                                  du_canon'45'reflects'45''7580'_832 (coe v0)
                                  (coe
                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v12)
                                     (coe
                                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                                        (coe MAlonzo.Code.Once.Type.C_pure_34))
                                     (coe v1))
                                  (coe v14) (coe v3) (coe v7) (coe v18))
                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_518 v13
                          -> coe
                               MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_518
                               (coe
                                  du_canon'45'reflects'45''7522'_804 (coe v0) (coe v1) (coe v2)
                                  (coe v3) (coe v4) (coe v13))
                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_622 v14
                          -> case coe v1 of
                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v15 v16 v17
                                 -> coe
                                      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_622
                                      (coe
                                         du_canon'45'reflects'45''7580'_832 (coe v0)
                                         (coe
                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v15)
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
                          du_reflect'45'app'45'var'45''7580'_848 (coe v0) (coe v1) (coe v2)
                          (coe
                             MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                             (coe
                                MAlonzo.Code.Once.Parser.Module.Resolve.d_elemStr_194 (coe v10)
                                (coe v3))
                             (coe
                                MAlonzo.Code.Once.Parser.Module.Resolve.d_isBuiltinName_192
                                (coe v10)))
                          (coe v3) (coe v8) (coe v5)
                   MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
                     -> case coe v10 of
                          MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v12
                            -> coe
                                 du_reflect'45'app2'45'var'45''7580'_884 (coe v0) (coe v1)
                                 (coe
                                    MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                                    (coe
                                       MAlonzo.Code.Once.Parser.Module.Resolve.d_elemStr_194
                                       (coe v12) (coe v3))
                                    (coe
                                       MAlonzo.Code.Once.Parser.Module.Resolve.d_isBuiltinName_192
                                       (coe v12)))
                                 (coe v3) (coe v11) (coe v8) (coe v5)
                          _ -> coe v9
                   _ -> coe v9)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v7 v8
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_536 v15 v18
                  -> case coe v1 of
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v19 v20 v21
                         -> coe
                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_536 v15
                              (coe
                                 du_canon'45'reflects'45''7580'_832
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402
                                    (coe v0) (coe v7) (coe v19))
                                 (coe v21)
                                 (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v15 v2)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v7) (coe v3))
                                 (coe v8) (coe v18))
                       _ -> coe v6
                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_518 v13
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_518
                       (coe
                          du_canon'45'reflects'45''7522'_804 (coe v0) (coe v1) (coe v2)
                          (coe v3) (coe v4) (coe v13))
                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_622 v14
                  -> case coe v1 of
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v15 v16 v17
                         -> coe
                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_622
                              (coe
                                 du_canon'45'reflects'45''7580'_832 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v15)
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
                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_552 v14 v15 v16 v17
                  -> case coe v1 of
                       MAlonzo.Code.Once.Type.C__'42'__122 v18 v19
                         -> coe
                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_552
                              v14 v15
                              (coe
                                 du_canon'45'reflects'45''7580'_832 (coe v0) (coe v18) (coe v14)
                                 (coe v3) (coe v7) (coe v16))
                              (coe
                                 du_canon'45'reflects'45''7580'_832 (coe v0) (coe v19) (coe v15)
                                 (coe v3) (coe v8) (coe v17))
                       _ -> coe v6
                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_518 v13
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_518
                       (coe
                          du_canon'45'reflects'45''7522'_804 (coe v0) (coe v1) (coe v2)
                          (coe v3) (coe v4) (coe v13))
                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_622 v14
                  -> case coe v1 of
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v15 v16 v17
                         -> coe
                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_622
                              (coe
                                 du_canon'45'reflects'45''7580'_832 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v15)
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
d_reflect'45'app'45'var'45''7580'_848 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
d_reflect'45'app'45'var'45''7580'_848 v0 v1 v2 v3 v4 ~v5 v6 ~v7 ~v8
                                      v9
  = du_reflect'45'app'45'var'45''7580'_848 v0 v1 v2 v3 v4 v6 v9
du_reflect'45'app'45'var'45''7580'_848 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
du_reflect'45'app'45'var'45''7580'_848 v0 v1 v2 v3 v4 v5 v6
  = if coe v3
      then case coe v6 of
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'curry'45'check_494 v13
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v14 v15 v16
                      -> case coe v16 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v17 v18 v19
                             -> coe
                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'curry'45'check_494
                                  (coe
                                     du_canon'45'reflects'45''7580'_832 (coe v0)
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'42'__122 (coe v14) (coe v17))
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                                           (coe MAlonzo.Code.Once.Type.C_pure_34))
                                        (coe v19))
                                     (coe v2) (coe v4) (coe v5) (coe v13))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'cata'45'check_508 v12 v14
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v15 v16 v17
                      -> case coe v15 of
                           MAlonzo.Code.Once.Type.C_μ'45'type_128 v18
                             -> case coe v16 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v19 v20
                                    -> coe
                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'cata'45'check_508
                                         v12
                                         (coe
                                            du_canon'45'reflects'45''7580'_832
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                                  (coe v0))
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364
                                                  (coe v0)))
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
                                            (coe v4) (coe v5) (coe v14))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_518 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_518
                    (coe
                       du_reflect'45'app'45'var'45''7522'_820 (coe v0) (coe v1) (coe v3)
                       (coe v4) (coe v5) (coe v11))
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_564 v10 v11 v13
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_128 v14
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_564
                           v10 v11
                           (coe
                              du_canon'45'reflects'45''7580'_832 (coe v0)
                              (coe
                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v14) (coe v1))
                              (coe v11) (coe v4) (coe v5) (coe v13))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_576 v9 v11 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_576 v9
                    v11
                    (coe
                       du_canon'45'reflects'45''7522'_804 (coe v0)
                       (coe
                          MAlonzo.Code.Once.Type.C__'42'__122
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v9)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe v1))
                          (coe v9))
                       (coe v11) (coe v4) (coe v5) (coe v12))
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_588 v11 v12
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v13 v14
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_588
                           v11
                           (coe
                              du_canon'45'reflects'45''7580'_832 (coe v0) (coe v13) (coe v11)
                              (coe v4) (coe v5) (coe v12))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_600 v11 v12
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v13 v14
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_600
                           v11
                           (coe
                              du_canon'45'reflects'45''7580'_832 (coe v0) (coe v14) (coe v11)
                              (coe v4) (coe v5) (coe v12))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_610 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_610
                    v10
                    (coe
                       du_canon'45'reflects'45''7580'_832 (coe v0)
                       (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v10) (coe v4) (coe v5)
                       (coe v11))
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_622 v12
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_622
                           (coe
                              du_reflect'45'app'45'var'45''7580'_848 (coe v0)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe MAlonzo.Code.Once.Type.C_pure_34))
                                 (coe v15))
                              (coe v2) (coe v3) (coe v4) (coe v5) (coe v12))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_638 v10 v12 v13 v15 v16
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_638
                    v10 v12 v13
                    (coe
                       du_canon'45'reflects'45''7522'_804 (coe v0) (coe v10) (coe v13)
                       (coe v4) (coe v5) (coe v15))
                    v16
             _ -> MAlonzo.RTE.mazUnreachableError
      else (case coe v6 of
              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_518 v11
                -> coe
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_518
                     (coe
                        du_reflect'45'app'45'var'45''7522'_820 (coe v0) (coe v1) (coe v3)
                        (coe v4) (coe v5) (coe v11))
              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_622 v12
                -> case coe v1 of
                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
                       -> coe
                            MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_622
                            (coe
                               du_reflect'45'app'45'var'45''7580'_848 (coe v0)
                               (coe
                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v13)
                                  (coe
                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                                     (coe MAlonzo.Code.Once.Type.C_pure_34))
                                  (coe v15))
                               (coe v2) (coe v3) (coe v4) (coe v5) (coe v12))
                     _ -> MAlonzo.RTE.mazUnreachableError
              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_638 v10 v12 v13 v15 v16
                -> coe
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_638
                     v10 v12 v13
                     (coe
                        du_canon'45'reflects'45''7522'_804 (coe v0) (coe v10) (coe v13)
                        (coe v4) (coe v5) (coe v15))
                     (coe
                        du_reflect'45'var'45''7580'_722
                        (coe
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v10)
                           (coe
                              MAlonzo.Code.Once.Type.C_mk'45'kind_50
                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                              (coe MAlonzo.Code.Once.Type.C_pure_34))
                           (coe v1))
                        (coe v3) (coe v16))
              _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Adequacy.CanonReflectMutual.reflect-app2-var-ᵢ
d_reflect'45'app2'45'var'45''7522'_866 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
d_reflect'45'app2'45'var'45''7522'_866 v0 v1 ~v2 v3 v4 ~v5 v6 v7
                                       ~v8 ~v9 v10
  = du_reflect'45'app2'45'var'45''7522'_866 v0 v1 v3 v4 v6 v7 v10
du_reflect'45'app2'45'var'45''7522'_866 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10
du_reflect'45'app2'45'var'45''7522'_866 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_342 v10 v12 v13 v14 v16 v17
        -> coe
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_342 v10 v12 v13 v14
             (coe
                du_reflect'45'app'45'var'45''7522'_820 (coe v0)
                (coe
                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v10)
                   (coe
                      MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v12)
                      (coe MAlonzo.Code.Once.Type.C_pure_34))
                   (coe v1))
                (coe v2) (coe v3) (coe v4) (coe v16))
             (coe
                du_canon'45'reflects'45''7580'_832 (coe v0) (coe v10) (coe v14)
                (coe v3) (coe v5) (coe v17))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_358 v10 v12 v13 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v17 v18 v19
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_358 v10 v12 v13
                    (coe
                       du_reflect'45'app'45'var'45''7522'_820 (coe v0)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v10)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_eff_36))
                          (coe v19))
                       (coe v2) (coe v3) (coe v4) (coe v15))
                    (coe
                       du_canon'45'reflects'45''7580'_832 (coe v0) (coe v10) (coe v13)
                       (coe v3) (coe v5) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CanonReflectMutual.reflect-app2-var-ᶜ
d_reflect'45'app2'45'var'45''7580'_884 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
d_reflect'45'app2'45'var'45''7580'_884 v0 v1 ~v2 v3 v4 ~v5 v6 v7
                                       ~v8 ~v9 v10
  = du_reflect'45'app2'45'var'45''7580'_884 v0 v1 v3 v4 v6 v7 v10
du_reflect'45'app2'45'var'45''7580'_884 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Bool ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16
du_reflect'45'app2'45'var'45''7580'_884 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = case coe v6 of
              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_518 v11
                -> coe
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_518
                     (coe
                        du_reflect'45'app2'45'var'45''7522'_866 (coe v0) (coe v1) (coe v2)
                        (coe v3) (coe v4) (coe v5) (coe v11))
              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_622 v12
                -> case coe v1 of
                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
                       -> coe
                            MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_622
                            (coe
                               du_reflect'45'app2'45'var'45''7580'_884 (coe v0)
                               (coe
                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v13)
                                  (coe
                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                                     (coe MAlonzo.Code.Once.Type.C_pure_34))
                                  (coe v15))
                               (coe v2) (coe v3) (coe v4) (coe v5) (coe v12))
                     _ -> MAlonzo.RTE.mazUnreachableError
              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_638 v10 v12 v13 v15 v16
                -> coe
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_638
                     v10 v12 v13
                     (coe
                        du_canon'45'reflects'45''7522'_804 (coe v0) (coe v10) (coe v13)
                        (coe v3) (coe v5) (coe v15))
                     (coe
                        du_reflect'45'app'45'var'45''7580'_848 (coe v0)
                        (coe
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v10)
                           (coe
                              MAlonzo.Code.Once.Type.C_mk'45'kind_50
                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                              (coe MAlonzo.Code.Once.Type.C_pure_34))
                           (coe v1))
                        (coe v12) (coe v2) (coe v3) (coe v4) (coe v16))
              _ -> MAlonzo.RTE.mazUnreachableError in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Bool.C_true_10
           -> case coe v6 of
                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check_442 v12 v15 v16 v18 v19
                  -> case coe v1 of
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v20 v21 v22
                         -> case coe v21 of
                              MAlonzo.Code.Once.Type.C_mk'45'kind_50 v23 v24
                                -> coe
                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check_442
                                     v12 v15 v16
                                     (coe
                                        du_canon'45'reflects'45''7580'_832 (coe v0)
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v12)
                                           (coe
                                              MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                              (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v24))
                                           (coe v22))
                                        (coe v15) (coe v3) (coe v4) (coe v18))
                                     (coe
                                        du_canon'45'reflects'45''7580'_832 (coe v0)
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v20)
                                           (coe
                                              MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                              (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v24))
                                           (coe v12))
                                        (coe v16) (coe v3) (coe v5) (coe v19))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v7
                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case'45'copair'45'check_462 v15 v16 v17 v18
                  -> case coe v1 of
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v19 v20 v21
                         -> case coe v19 of
                              MAlonzo.Code.Once.Type.C__'43'__124 v22 v23
                                -> case coe v20 of
                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50 v24 v25
                                       -> coe
                                            MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case'45'copair'45'check_462
                                            v15 v16
                                            (coe
                                               du_canon'45'reflects'45''7580'_832 (coe v0)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                  (coe v22)
                                                  (coe
                                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                     (coe v25))
                                                  (coe v21))
                                               (coe v15) (coe v3) (coe v4) (coe v17))
                                            (coe
                                               du_canon'45'reflects'45''7580'_832 (coe v0)
                                               (coe
                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                  (coe v23)
                                                  (coe
                                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                     (coe v25))
                                                  (coe v21))
                                               (coe v16) (coe v3) (coe v5) (coe v18))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> coe v7
                       _ -> coe v7
                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'morph'45'check_480 v14 v15 v16 v17
                  -> case coe v1 of
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v18 v19 v20
                         -> case coe v20 of
                              MAlonzo.Code.Once.Type.C__'42'__122 v21 v22
                                -> coe
                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'morph'45'check_480
                                     v14 v15
                                     (coe
                                        du_canon'45'reflects'45''7580'_832 (coe v0)
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v18)
                                           (coe
                                              MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                                              (coe MAlonzo.Code.Once.Type.C_pure_34))
                                           (coe v21))
                                        (coe v14) (coe v3) (coe v4) (coe v16))
                                     (coe
                                        du_canon'45'reflects'45''7580'_832 (coe v0)
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v18)
                                           (coe
                                              MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                                              (coe MAlonzo.Code.Once.Type.C_pure_34))
                                           (coe v22))
                                        (coe v15) (coe v3) (coe v5) (coe v17))
                              _ -> coe v7
                       _ -> coe v7
                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_518 v12
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_518
                       (coe
                          du_reflect'45'app2'45'var'45''7522'_866 (coe v0) (coe v1) (coe v2)
                          (coe v3) (coe v4) (coe v5) (coe v12))
                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_622 v13
                  -> case coe v1 of
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v14 v15 v16
                         -> coe
                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_622
                              (coe
                                 du_reflect'45'app2'45'var'45''7580'_884 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v14)
                                    (coe
                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                       (coe MAlonzo.Code.Once.Type.C_Many_10)
                                       (coe MAlonzo.Code.Once.Type.C_pure_34))
                                    (coe v16))
                                 (coe v2) (coe v3) (coe v4) (coe v5) (coe v13))
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_638 v11 v13 v14 v16 v17
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_638
                       v11 v13 v14
                       (coe
                          du_canon'45'reflects'45''7522'_804 (coe v0) (coe v11) (coe v14)
                          (coe v3) (coe v5) (coe v16))
                       (coe
                          du_reflect'45'app'45'var'45''7580'_848 (coe v0)
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v11)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe v1))
                          (coe v13) (coe v2) (coe v3) (coe v4) (coe v17))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v7)
