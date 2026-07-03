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

module MAlonzo.Code.Once.TypeCheck.Completeness where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Functor.Decide
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.TypeCheck.Completeness.infer-complete-RInt
d_infer'45'complete'45'RInt_16 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RInt_16 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_int_360 v1)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192 (coe v0))
            erased))
-- Once.TypeCheck.Completeness.infer-complete-RStringLit
d_infer'45'complete'45'RStringLit_30 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RStringLit_30 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_str_366 v1)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192 (coe v0))
            erased))
-- Once.TypeCheck.Completeness.infer-complete-RUnit
d_infer'45'complete'45'RUnit_42 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RUnit_42 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_328)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192 (coe v0))
            erased))
-- Once.TypeCheck.Completeness.infer-complete-RVar-unit
d_infer'45'complete'45'RVar'45'unit_52 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RVar'45'unit_52 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_328)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192 (coe v0))
            erased))
-- Once.TypeCheck.Completeness.infer-complete-RQualified
d_infer'45'complete'45'RQualified_68 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RQualified_68 v0 v1 v2 v3 ~v4
  = du_infer'45'complete'45'RQualified_68 v0 v1 v2 v3
du_infer'45'complete'45'RQualified_68 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RQualified_68 v0 v1 v2 v3
  = coe du_go_100 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.TypeCheck.Completeness._.helper
d_helper_88 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helper_88 = erased
-- Once.TypeCheck.Completeness._.go
d_go_100 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_100 v0 v1 v2 ~v3 ~v4 v5 ~v6 = du_go_100 v0 v1 v2 v5
du_go_100 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_100 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Type.C_Unit_122
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_504
                (MAlonzo.Code.Once.CanonicalName.d_bare_12
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("." :: Data.Text.Text) v1))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C_Void_124
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_504
                (MAlonzo.Code.Once.CanonicalName.d_bare_12
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("." :: Data.Text.Text) v1))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C__'42'__126 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_504
                (MAlonzo.Code.Once.CanonicalName.d_bare_12
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("." :: Data.Text.Text) v1))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C__'43'__128 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_504
                (MAlonzo.Code.Once.CanonicalName.d_bare_12
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("." :: Data.Text.Text) v1))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v4 v5 v6
        -> case coe v5 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v7 v8
               -> case coe v7 of
                    MAlonzo.Code.Once.Type.C_Zero_6
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_sigOp_504
                              (MAlonzo.Code.Once.CanonicalName.d_bare_12
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                       ("." :: Data.Text.Text) v1))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                    (coe v0))
                                 erased))
                    MAlonzo.Code.Once.Type.C_One_8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_sigOp_504
                              (MAlonzo.Code.Once.CanonicalName.d_bare_12
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                       ("." :: Data.Text.Text) v1))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                    (coe v0))
                                 erased))
                    MAlonzo.Code.Once.Type.C_Many_10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                              (coe
                                 MAlonzo.Code.Once.IR.C_SigOp_166
                                 (MAlonzo.Code.Once.TypeCheck.Elaborate.d_ext'45'arrow'45'info_2038
                                    (coe v4) (coe v6) (coe v0) (coe v2) (coe v1) (coe v8))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                    (coe v0))
                                 erased))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_132 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_504
                (MAlonzo.Code.Once.CanonicalName.d_bare_12
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("." :: Data.Text.Text) v1))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C_ν'45'type_134 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_504
                (MAlonzo.Code.Once.CanonicalName.d_bare_12
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("." :: Data.Text.Text) v1))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C_Int_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_504
                (MAlonzo.Code.Once.CanonicalName.d_bare_12
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("." :: Data.Text.Text) v1))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C_Float_138
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_504
                (MAlonzo.Code.Once.CanonicalName.d_bare_12
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("." :: Data.Text.Text) v1))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C_Str_140
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_504
                (MAlonzo.Code.Once.CanonicalName.d_bare_12
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("." :: Data.Text.Text) v1))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C_Buffer_142
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_504
                (MAlonzo.Code.Once.CanonicalName.d_bare_12
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("." :: Data.Text.Text) v1))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192 (coe v0))
                   erased))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.infer-complete-RResolved
d_infer'45'complete'45'RResolved_170 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RResolved_170 v0 v1 v2 ~v3
  = du_infer'45'complete'45'RResolved_170 v0 v1 v2
du_infer'45'complete'45'RResolved_170 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RResolved_170 v0 v1 v2
  = coe du_go_200 (coe v0) (coe v1) (coe v2)
-- Once.TypeCheck.Completeness._.helper
d_helper_188 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helper_188 = erased
-- Once.TypeCheck.Completeness._.go
d_go_200 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_200 v0 v1 ~v2 ~v3 v4 ~v5 = du_go_200 v0 v1 v4
du_go_200 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_200 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Type.C_Unit_122
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_504 v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C_Void_124
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_504 v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C__'42'__126 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_504 v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C__'43'__128 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_504 v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Type.C_Zero_6
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_504 v1)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                    (coe v0))
                                 erased))
                    MAlonzo.Code.Once.Type.C_One_8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_504 v1)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                    (coe v0))
                                 erased))
                    MAlonzo.Code.Once.Type.C_Many_10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                              (coe
                                 MAlonzo.Code.Once.IR.C_SigOp_166
                                 (MAlonzo.Code.Once.TypeCheck.Elaborate.d_ext'45'resolved'45'info_2050
                                    (coe v3) (coe v5) (coe v0) (coe v1) (coe v7))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                    (coe v0))
                                 erased))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_132 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_504 v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C_ν'45'type_134 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_504 v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C_Int_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_504 v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C_Float_138
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_504 v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C_Str_140
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_504 v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C_Buffer_142
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Once.Surface.Syntax.C_sigOp_504 v1)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192 (coe v0))
                   erased))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.infer-complete-RPair
d_infer'45'complete'45'RPair_290 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RPair_290 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14
  = du_infer'45'complete'45'RPair_290 v0 v1 v2
du_infer'45'complete'45'RPair_290 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RPair_290 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v6 v7 v8 v9 v10
                  -> let v11
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
                               (coe v0) (coe v2) in
                     coe
                       (case coe v11 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                            -> case coe v12 of
                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v14 v15 v16 v17 v18
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_pair_252 v7 v15 v8
                                           v16)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe
                                              MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v9)
                                              (coe v17))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18)
                                              erased))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.infer-complete-RUnaryOp-neg
d_infer'45'complete'45'RUnaryOp'45'neg_348 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RUnaryOp'45'neg_348 v0 v1 ~v2 ~v3 ~v4 ~v5
                                           ~v6
  = du_infer'45'complete'45'RUnaryOp'45'neg_348 v0 v1
du_infer'45'complete'45'RUnaryOp'45'neg_348 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RUnaryOp'45'neg_348 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v5 v6 v7 v8 v9
                  -> coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe MAlonzo.Code.Once.Surface.Syntax.C_neg_424 v7)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe addInt (coe (1 :: Integer)) (coe v8))
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased)))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.infer-complete-RAnnot
d_infer'45'complete'45'RAnnot_386 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RAnnot_386 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_infer'45'complete'45'RAnnot_386 v0 v1 v2
du_infer'45'complete'45'RAnnot_386 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RAnnot_386 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_1666
              (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_328 v6 v7 v8 v9
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.infer-complete-RLet
d_infer'45'complete'45'RLet_444 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RLet_444 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                                ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16
  = du_infer'45'complete'45'RLet_444 v0 v1 v2 v3
du_infer'45'complete'45'RLet_444 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RLet_444 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
              (coe v0) (coe v2) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v7 v8 v9 v10 v11
                  -> let v12
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
                               (coe
                                  MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_234 (coe v0)
                                  (coe v1) (coe v7))
                               (coe v3) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                            -> case coe v13 of
                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v15 v16 v17 v18 v19
                                   -> case coe v16 of
                                        MAlonzo.Code.Once.Surface.Syntax.C__'8759'__66 v21 v22
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.C_let''_354 v8
                                                  v22 v21 v7 v9 v17)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                     (coe v10)
                                                     (coe addInt (coe (1 :: Integer)) (coe v18)))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v19) erased))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.infer-complete-RApp-id
d_infer'45'complete'45'RApp'45'id_516 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RApp'45'id_516 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_infer'45'complete'45'RApp'45'id_516 v0 v1
du_infer'45'complete'45'RApp'45'id_516 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'id_516 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v5 v6 v7 v8 v9
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_546 v6 v5
                          (coe MAlonzo.Code.Once.IR.C_id_22) v7)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe addInt (coe (1 :: Integer)) (coe v8))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.infer-complete-RApp-terminal
d_infer'45'complete'45'RApp'45'terminal_554 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RApp'45'terminal_554 v0 v1 ~v2 ~v3 ~v4 ~v5
                                            ~v6 ~v7
  = du_infer'45'complete'45'RApp'45'terminal_554 v0 v1
du_infer'45'complete'45'RApp'45'terminal_554 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'terminal_554 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v5 v6 v7 v8 v9
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_546 v6 v5
                          (coe MAlonzo.Code.Once.IR.C_terminal_74) v7)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe addInt (coe (1 :: Integer)) (coe v8))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.infer-complete-RApp-fst
d_infer'45'complete'45'RApp'45'fst_594 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RApp'45'fst_594 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 ~v8
  = du_infer'45'complete'45'RApp'45'fst_594 v0 v1
du_infer'45'complete'45'RApp'45'fst_594 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'fst_594 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v5 v6 v7 v8 v9
                  -> coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_546 v6 v5
                             (coe MAlonzo.Code.Once.IR.C_fst_44) v7)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe addInt (coe (1 :: Integer)) (coe v8))
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased)))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.infer-complete-RApp-snd
d_infer'45'complete'45'RApp'45'snd_634 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RApp'45'snd_634 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 ~v8
  = du_infer'45'complete'45'RApp'45'snd_634 v0 v1
du_infer'45'complete'45'RApp'45'snd_634 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'snd_634 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v5 v6 v7 v8 v9
                  -> coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_546 v6 v5
                             (coe MAlonzo.Code.Once.IR.C_snd_50) v7)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe addInt (coe (1 :: Integer)) (coe v8))
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased)))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.infer-complete-RApp-apply
d_infer'45'complete'45'RApp'45'apply_674 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RApp'45'apply_674 v0 v1 v2 ~v3 ~v4 ~v5 ~v6
                                         ~v7 ~v8
  = du_infer'45'complete'45'RApp'45'apply_674 v0 v1 v2
du_infer'45'complete'45'RApp'45'apply_674 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'apply_674 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v6 v7 v8 v9 v10
                  -> case coe v6 of
                       MAlonzo.Code.Once.Type.C__'42'__126 v11 v12
                         -> case coe v11 of
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v13 v14 v15
                                -> case coe v14 of
                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50 v16 v17
                                       -> coe
                                            seq (coe v16)
                                            (coe
                                               seq (coe v17)
                                               (let v18
                                                      = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__228
                                                          (coe v2) (coe v2) in
                                                coe
                                                  (case coe v18 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v19 v20
                                                       -> if coe v19
                                                            then coe
                                                                   seq (coe v20)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe
                                                                         MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_546
                                                                         v7
                                                                         (coe
                                                                            MAlonzo.Code.Once.Type.C__'42'__126
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                                                               (coe v2)
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Type.C_Many_10)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Type.C_pure_34))
                                                                               (coe v15))
                                                                            (coe v2))
                                                                         (coe
                                                                            MAlonzo.Code.Once.IR.C_apply_96)
                                                                         v8)
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                         (coe
                                                                            addInt
                                                                            (coe (1 :: Integer))
                                                                            (coe v9))
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                            (coe v10) erased)))
                                                            else coe
                                                                   seq (coe v20)
                                                                   (coe
                                                                      MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                     _ -> MAlonzo.RTE.mazUnreachableError)))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.infer-complete-RVar-local
d_infer'45'complete'45'RVar'45'local_740 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RVar'45'local_740 v0 v1 ~v2 ~v3 v4 ~v5 ~v6
  = du_infer'45'complete'45'RVar'45'local_740 v0 v1 v4
du_infer'45'complete'45'RVar'45'local_740 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RVar'45'local_740 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v3 ->
                 coe
                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                   (coe v1))
              (coe
                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v1)
                 (coe ("unit" :: Data.Text.Text))) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe
                       seq (coe v5) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                else coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192 (coe v0))
                                erased)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness._.helper
d_helper_800 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helper_800 = erased
-- Once.TypeCheck.Completeness.infer-complete-RVar-import
d_infer'45'complete'45'RVar'45'import_814 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RVar'45'import_814 v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_infer'45'complete'45'RVar'45'import_814 v0 v1
du_infer'45'complete'45'RVar'45'import_814 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RVar'45'import_814 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v2 ->
                 coe
                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                   (coe v1))
              (coe
                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v1)
                 (coe ("unit" :: Data.Text.Text))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe
                       seq (coe v4) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                else coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_sigOp_504
                             (MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v1)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192 (coe v0))
                                erased)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness._.helperLoc
d_helperLoc_868 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helperLoc_868 = erased
-- Once.TypeCheck.Completeness._.helperImp
d_helperImp_874 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helperImp_874 = erased
-- Once.TypeCheck.Completeness.infer-complete-RBinOp-arith
d_infer'45'complete'45'RBinOp'45'arith_908 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RBinOp'45'arith_908 v0 v1 ~v2 v3 v4 ~v5 ~v6
                                           ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14
  = du_infer'45'complete'45'RBinOp'45'arith_908 v0 v1 v3 v4
du_infer'45'complete'45'RBinOp'45'arith_908 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RBinOp'45'arith_908 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
        -> let v4
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_add_376
                                                        v8 v16 v9 v17)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe
                                                           MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                           (coe v10) (coe v18))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v19) erased)))
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
        -> let v4
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_sub_386
                                                        v8 v16 v9 v17)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe
                                                           MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                           (coe v10) (coe v18))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v19) erased)))
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
        -> let v4
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_mul_396
                                                        v8 v16 v9 v17)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe
                                                           MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                           (coe v10) (coe v18))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v19) erased)))
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14
        -> let v4
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_div_406
                                                        v8 v16 v9 v17)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe
                                                           MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                           (coe v10) (coe v18))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v19) erased)))
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpMod_16
        -> let v4
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_mod''_416
                                                        v8 v16 v9 v17)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe
                                                           MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                           (coe v10) (coe v18))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v19) erased)))
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.infer-complete-RBinOp-cmp
d_infer'45'complete'45'RBinOp'45'cmp_1132 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RBinOp'45'cmp_1132 v0 v1 ~v2 v3 v4 ~v5 ~v6
                                          ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14
  = du_infer'45'complete'45'RBinOp'45'cmp_1132 v0 v1 v3 v4
du_infer'45'complete'45'RBinOp'45'cmp_1132 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RBinOp'45'cmp_1132 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpLt_18
        -> let v4
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_lt_434 v8
                                                        v16 v9 v17)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe
                                                           MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                           (coe v10) (coe v18))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v19) erased)))
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpLe_20
        -> let v4
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_le_444 v8
                                                        v16 v9 v17)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe
                                                           MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                           (coe v10) (coe v18))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v19) erased)))
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpGt_22
        -> let v4
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_gt_454 v8
                                                        v16 v9 v17)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe
                                                           MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                           (coe v10) (coe v18))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v19) erased)))
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpGe_24
        -> let v4
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_ge_464 v8
                                                        v16 v9 v17)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe
                                                           MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                           (coe v10) (coe v18))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v19) erased)))
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpEq_26
        -> let v4
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_eq_474 v8
                                                        v16 v9 v17)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe
                                                           MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                           (coe v10) (coe v18))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v19) erased)))
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpNe_28
        -> let v4
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_ne_484 v8
                                                        v16 v9 v17)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe
                                                           MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                           (coe v10) (coe v18))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe v19) erased)))
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.decideLeq-just
d_decideLeq'45'just_1368 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_decideLeq'45'just_1368 v0 v1 ~v2
  = du_decideLeq'45'just_1368 v0 v1
du_decideLeq'45'just_1368 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_decideLeq'45'just_1368 v0 v1
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
-- Once.TypeCheck.Completeness.check-complete-RLam
d_check'45'complete'45'RLam_1398 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_check'45'complete'45'RLam_1398 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9
                                 ~v10 ~v11 ~v12
  = du_check'45'complete'45'RLam_1398 v0 v1 v2 v3 v4 v5 v6
du_check'45'complete'45'RLam_1398 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_check'45'complete'45'RLam_1398 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_1666
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_234 (coe v0)
                 (coe v1) (coe v3))
              (coe v2) (coe v6) in
    coe
      (case coe v7 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
           -> case coe v8 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_328 v10 v11 v12 v13
                  -> coe
                       seq (coe v10)
                       (let v14
                              = MAlonzo.Code.Once.TypeCheck.Elaborate.d_decideLeq_1468
                                  (coe v5) (coe v4) in
                        coe
                          (let v15 = coe du_decideLeq'45'just_1368 (coe v5) (coe v4) in
                           coe
                             (coe
                                seq (coe v14)
                                (coe
                                   seq (coe v15)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                      (coe MAlonzo.Code.Once.Surface.Syntax.C_lam_208 v5 v11)
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe addInt (coe (1 :: Integer)) (coe v12))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                            erased)))))))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.check-complete-RLam-eff
d_check'45'complete'45'RLam'45'eff_1488 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_check'45'complete'45'RLam'45'eff_1488 v0 v1 v2 v3 v4 v5 ~v6 ~v7
                                        ~v8 ~v9 ~v10 ~v11
  = du_check'45'complete'45'RLam'45'eff_1488 v0 v1 v2 v3 v4 v5
du_check'45'complete'45'RLam'45'eff_1488 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_check'45'complete'45'RLam'45'eff_1488 v0 v1 v2 v3 v4 v5
  = let v6
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_1666
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_234 (coe v0)
                 (coe v1) (coe v3))
              (coe v2) (coe v5) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
           -> case coe v7 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_328 v9 v10 v11 v12
                  -> coe
                       seq (coe v9)
                       (let v13
                              = MAlonzo.Code.Once.TypeCheck.Elaborate.d_decideLeq_1468
                                  (coe v4) (coe MAlonzo.Code.Once.Type.C_Many_10) in
                        coe
                          (let v14
                                 = coe
                                     du_decideLeq'45'just_1368 (coe v4)
                                     (coe MAlonzo.Code.Once.Type.C_Many_10) in
                           coe
                             (coe
                                seq (coe v13)
                                (coe
                                   seq (coe v14)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                      (coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_arr''_496
                                         (coe MAlonzo.Code.Once.Surface.Syntax.C_lam_208 v4 v10))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe addInt (coe (1 :: Integer)) (coe v11))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                            erased)))))))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.infer-complete-RDestruct
d_infer'45'complete'45'RDestruct_1598 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RDestruct_1598 v0 v1 v2 v3 v4 v5 ~v6 ~v7 ~v8
                                      ~v9 ~v10 ~v11 v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21
                                      ~v22 ~v23 ~v24 ~v25
  = du_infer'45'complete'45'RDestruct_1598 v0 v1 v2 v3 v4 v5 v12
du_infer'45'complete'45'RDestruct_1598 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RDestruct_1598 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
              (coe v0) (coe v1) in
    coe
      (case coe v7 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
           -> case coe v8 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v10 v11 v12 v13 v14
                  -> case coe v10 of
                       MAlonzo.Code.Once.Type.C__'43'__128 v15 v16
                         -> let v17
                                  = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_234
                                         (coe v0) (coe v2) (coe v15))
                                      (coe v3) in
                            coe
                              (case coe v17 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                   -> case coe v18 of
                                        MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v20 v21 v22 v23 v24
                                          -> case coe v21 of
                                               MAlonzo.Code.Once.Surface.Syntax.C__'8759'__66 v26 v27
                                                 -> let v28
                                                          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
                                                              (coe
                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_234
                                                                 (coe v0) (coe v4) (coe v16))
                                                              (coe v5) in
                                                    coe
                                                      (case coe v28 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v29 v30
                                                           -> case coe v29 of
                                                                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v31 v32 v33 v34 v35
                                                                  -> case coe v32 of
                                                                       MAlonzo.Code.Once.Surface.Syntax.C__'8759'__66 v37 v38
                                                                         -> let v39
                                                                                  = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__228
                                                                                      (coe v6)
                                                                                      (coe v6) in
                                                                            coe
                                                                              (case coe v39 of
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v40 v41
                                                                                   -> if coe v40
                                                                                        then coe
                                                                                               seq
                                                                                               (coe
                                                                                                  v41)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.Surface.Syntax.C_case''_322
                                                                                                     v11
                                                                                                     v27
                                                                                                     v38
                                                                                                     v26
                                                                                                     v37
                                                                                                     v15
                                                                                                     v16
                                                                                                     v12
                                                                                                     v22
                                                                                                     v33)
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                           (coe
                                                                                                              v13)
                                                                                                           (coe
                                                                                                              addInt
                                                                                                              (coe
                                                                                                                 (1 ::
                                                                                                                    Integer))
                                                                                                              (coe
                                                                                                                 v23)))
                                                                                                        (coe
                                                                                                           addInt
                                                                                                           (coe
                                                                                                              (1 ::
                                                                                                                 Integer))
                                                                                                           (coe
                                                                                                              v34)))
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                        (coe
                                                                                                           v35)
                                                                                                        erased)))
                                                                                        else coe
                                                                                               seq
                                                                                               (coe
                                                                                                  v41)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.infer-complete-RApp-generic
d_infer'45'complete'45'RApp'45'generic_1796 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RApp'45'generic_1796 v0 v1 v2 v3 ~v4 v5 ~v6
                                            ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16
  = du_infer'45'complete'45'RApp'45'generic_1796 v0 v1 v2 v3 v5
du_infer'45'complete'45'RApp'45'generic_1796 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'generic_1796 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
              (coe v0) (coe v1) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> case coe v6 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v8 v9 v10 v11 v12
                  -> let v13
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_1666
                               (coe v0) (coe v2) (coe v3) in
                     coe
                       (case coe v13 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                            -> case coe v14 of
                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_328 v16 v17 v18 v19
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_app_224 v9 v16 v3 v4
                                           v10 v17)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe
                                              MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v11)
                                              (coe v18))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v19)
                                              erased))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.viewBridge
d_viewBridge_1808 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_AppHeadView_852 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_viewBridge_1808 = erased
-- Once.TypeCheck.Completeness.otherBridge
d_otherBridge_1820 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Classify.T_PolyBuiltinApp_822 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_otherBridge_1820 = erased
-- Once.TypeCheck.Completeness.infer-complete-RApp-eff
d_infer'45'complete'45'RApp'45'eff_1924 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RApp'45'eff_1924 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7
                                        ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15
  = du_infer'45'complete'45'RApp'45'eff_1924 v0 v1 v2 v3
du_infer'45'complete'45'RApp'45'eff_1924 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'eff_1924 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658
              (coe v0) (coe v1) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v7 v8 v9 v10 v11
                  -> let v12
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_1666
                               (coe v0) (coe v2) (coe v3) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                            -> case coe v13 of
                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_328 v15 v16 v17 v18
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_effApp_238 v8 v15 v3
                                           v9 v16)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe
                                              MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v10)
                                              (coe v17))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18)
                                              erased))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.checkElab-fallback-RVar
d_checkElab'45'fallback'45'RVar_2010 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar_2010 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_checkElab'45'fallback'45'RVar_2010 v0 v1 v2
du_checkElab'45'fallback'45'RVar_2010 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar_2010 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v3 ->
                 coe
                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                   (coe v1))
              (coe
                 MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                 (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                 (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v1)
                 (coe
                    MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                    ("id" :: Data.Text.Text))) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then let v6
                           = seq
                               (coe v5)
                               (coe MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'id_1106) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'id_1106
                            -> let v7
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1854
                                         (coe v0) (coe ("id" :: Data.Text.Text))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_186
                                               (coe v0))
                                            (coe ("id" :: Data.Text.Text))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_named_188
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190
                                               (coe v0)))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                               (coe v0))
                                            (coe ("id" :: Data.Text.Text))) in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                      -> case coe v8 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v10 v11 v12 v13 v14
                                             -> let v15
                                                      = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__228
                                                          (coe v2) (coe v2) in
                                                coe
                                                  (case coe v15 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                       -> if coe v16
                                                            then coe
                                                                   seq (coe v17)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe v12)
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                         (coe v13)
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                            (coe v14) erased)))
                                                            else coe
                                                                   seq (coe v17)
                                                                   (coe
                                                                      MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'fst_1108
                            -> let v7
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1854
                                         (coe v0) (coe ("fst" :: Data.Text.Text))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_186
                                               (coe v0))
                                            (coe ("fst" :: Data.Text.Text))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_named_188
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190
                                               (coe v0)))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                               (coe v0))
                                            (coe ("fst" :: Data.Text.Text))) in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                      -> case coe v8 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v10 v11 v12 v13 v14
                                             -> let v15
                                                      = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__228
                                                          (coe v2) (coe v2) in
                                                coe
                                                  (case coe v15 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                       -> if coe v16
                                                            then coe
                                                                   seq (coe v17)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe v12)
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                         (coe v13)
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                            (coe v14) erased)))
                                                            else coe
                                                                   seq (coe v17)
                                                                   (coe
                                                                      MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'snd_1110
                            -> let v7
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1854
                                         (coe v0) (coe ("snd" :: Data.Text.Text))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_186
                                               (coe v0))
                                            (coe ("snd" :: Data.Text.Text))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_named_188
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190
                                               (coe v0)))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                               (coe v0))
                                            (coe ("snd" :: Data.Text.Text))) in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                      -> case coe v8 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v10 v11 v12 v13 v14
                                             -> let v15
                                                      = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__228
                                                          (coe v2) (coe v2) in
                                                coe
                                                  (case coe v15 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                       -> if coe v16
                                                            then coe
                                                                   seq (coe v17)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe v12)
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                         (coe v13)
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                            (coe v14) erased)))
                                                            else coe
                                                                   seq (coe v17)
                                                                   (coe
                                                                      MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'terminal_1112
                            -> let v7
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1854
                                         (coe v0) (coe ("terminal" :: Data.Text.Text))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_186
                                               (coe v0))
                                            (coe ("terminal" :: Data.Text.Text))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_named_188
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190
                                               (coe v0)))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                               (coe v0))
                                            (coe ("terminal" :: Data.Text.Text))) in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                      -> case coe v8 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v10 v11 v12 v13 v14
                                             -> let v15
                                                      = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__228
                                                          (coe v2) (coe v2) in
                                                coe
                                                  (case coe v15 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                       -> if coe v16
                                                            then coe
                                                                   seq (coe v17)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe v12)
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                         (coe v13)
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                            (coe v14) erased)))
                                                            else coe
                                                                   seq (coe v17)
                                                                   (coe
                                                                      MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'initial_1114
                            -> let v7
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1854
                                         (coe v0) (coe ("initial" :: Data.Text.Text))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_186
                                               (coe v0))
                                            (coe ("initial" :: Data.Text.Text))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_named_188
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190
                                               (coe v0)))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                               (coe v0))
                                            (coe ("initial" :: Data.Text.Text))) in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                      -> case coe v8 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v10 v11 v12 v13 v14
                                             -> let v15
                                                      = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__228
                                                          (coe v2) (coe v2) in
                                                coe
                                                  (case coe v15 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                       -> if coe v16
                                                            then coe
                                                                   seq (coe v17)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe v12)
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                         (coe v13)
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                            (coe v14) erased)))
                                                            else coe
                                                                   seq (coe v17)
                                                                   (coe
                                                                      MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inl_1116
                            -> let v7
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1854
                                         (coe v0) (coe ("inl" :: Data.Text.Text))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_186
                                               (coe v0))
                                            (coe ("inl" :: Data.Text.Text))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_named_188
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190
                                               (coe v0)))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                               (coe v0))
                                            (coe ("inl" :: Data.Text.Text))) in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                      -> case coe v8 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v10 v11 v12 v13 v14
                                             -> let v15
                                                      = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__228
                                                          (coe v2) (coe v2) in
                                                coe
                                                  (case coe v15 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                       -> if coe v16
                                                            then coe
                                                                   seq (coe v17)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe v12)
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                         (coe v13)
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                            (coe v14) erased)))
                                                            else coe
                                                                   seq (coe v17)
                                                                   (coe
                                                                      MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inr_1118
                            -> let v7
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1854
                                         (coe v0) (coe ("inr" :: Data.Text.Text))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_186
                                               (coe v0))
                                            (coe ("inr" :: Data.Text.Text))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_named_188
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190
                                               (coe v0)))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                               (coe v0))
                                            (coe ("inr" :: Data.Text.Text))) in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                      -> case coe v8 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v10 v11 v12 v13 v14
                                             -> let v15
                                                      = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__228
                                                          (coe v2) (coe v2) in
                                                coe
                                                  (case coe v15 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                       -> if coe v16
                                                            then coe
                                                                   seq (coe v17)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe v12)
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                         (coe v13)
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                            (coe v14) erased)))
                                                            else coe
                                                                   seq (coe v17)
                                                                   (coe
                                                                      MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'other_1122
                            -> let v8
                                     = coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                         erased
                                         (\ v8 ->
                                            coe
                                              MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                              (coe v1))
                                         (coe
                                            MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                                            (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                               v1)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                               ("unit" :: Data.Text.Text))) in
                               coe
                                 (case coe v8 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                      -> if coe v9
                                           then let v11
                                                      = seq
                                                          (coe v10)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Unit_122)
                                                                (coe
                                                                   MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_70
                                                                   (coe
                                                                      MAlonzo.Code.Once.TypeCheck.Classify.d_size_186
                                                                      (coe v0)))
                                                                (coe
                                                                   MAlonzo.Code.Once.Surface.Syntax.C_unit_328)
                                                                (coe (0 :: Integer))
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                                   (coe v0)))
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_44)) in
                                                coe
                                                  (case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                       -> case coe v12 of
                                                            MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v14 v15 v16 v17 v18
                                                              -> let v19
                                                                       = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__228
                                                                           (coe v2) (coe v2) in
                                                                 coe
                                                                   (case coe v19 of
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                        -> if coe v20
                                                                             then coe
                                                                                    seq (coe v21)
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       (coe v16)
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                          (coe v17)
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                             (coe
                                                                                                v18)
                                                                                             erased)))
                                                                             else coe
                                                                                    seq (coe v21)
                                                                                    (coe
                                                                                       MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                           else (let v11
                                                       = seq
                                                           (coe v10)
                                                           (coe
                                                              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1854
                                                              (coe v0) (coe v1)
                                                              (coe
                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal_404
                                                                 (coe v0) (coe v1))
                                                              (coe
                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                                                 (coe
                                                                    MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                                                    (coe v0))
                                                                 (coe v1))) in
                                                 coe
                                                   (case coe v11 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                        -> case coe v12 of
                                                             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v14 v15 v16 v17 v18
                                                               -> let v19
                                                                        = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__228
                                                                            (coe v2) (coe v2) in
                                                                  coe
                                                                    (case coe v19 of
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                         -> if coe v20
                                                                              then coe
                                                                                     seq (coe v21)
                                                                                     (coe
                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                        (coe v16)
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                           (coe v17)
                                                                                           (coe
                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                              (coe
                                                                                                 v18)
                                                                                              erased)))
                                                                              else coe
                                                                                     seq (coe v21)
                                                                                     (coe
                                                                                        MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                                       _ -> MAlonzo.RTE.mazUnreachableError)
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                else (let v6
                            = seq
                                (coe v5)
                                (let v6
                                       = coe
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                           erased
                                           (\ v6 ->
                                              coe
                                                MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                (coe v1))
                                           (coe
                                              MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                              (coe v1) (coe ("fst" :: Data.Text.Text))) in
                                 coe
                                   (case coe v6 of
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                                        -> if coe v7
                                             then coe
                                                    seq (coe v8)
                                                    (coe
                                                       MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'fst_1108)
                                             else coe
                                                    seq (coe v8)
                                                    (let v9
                                                           = coe
                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                               erased
                                                               (\ v9 ->
                                                                  coe
                                                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                    (coe v1))
                                                               (coe
                                                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                  (coe v1)
                                                                  (coe
                                                                     ("snd" :: Data.Text.Text))) in
                                                     coe
                                                       (case coe v9 of
                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                                            -> if coe v10
                                                                 then coe
                                                                        seq (coe v11)
                                                                        (coe
                                                                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'snd_1110)
                                                                 else coe
                                                                        seq (coe v11)
                                                                        (let v12
                                                                               = coe
                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                   erased
                                                                                   (\ v12 ->
                                                                                      coe
                                                                                        MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                        (coe v1))
                                                                                   (coe
                                                                                      MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                      (coe v1)
                                                                                      (coe
                                                                                         ("terminal"
                                                                                          ::
                                                                                          Data.Text.Text))) in
                                                                         coe
                                                                           (case coe v12 of
                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                                                -> if coe v13
                                                                                     then coe
                                                                                            seq
                                                                                            (coe
                                                                                               v14)
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'terminal_1112)
                                                                                     else coe
                                                                                            seq
                                                                                            (coe
                                                                                               v14)
                                                                                            (let v15
                                                                                                   = coe
                                                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                       erased
                                                                                                       (\ v15 ->
                                                                                                          coe
                                                                                                            MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                            (coe
                                                                                                               v1))
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                          (coe
                                                                                                             v1)
                                                                                                          (coe
                                                                                                             ("initial"
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
                                                                                                                   MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'initial_1114)
                                                                                                         else coe
                                                                                                                seq
                                                                                                                (coe
                                                                                                                   v17)
                                                                                                                (let v18
                                                                                                                       = coe
                                                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                           erased
                                                                                                                           (\ v18 ->
                                                                                                                              coe
                                                                                                                                MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                (coe
                                                                                                                                   v1))
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                              (coe
                                                                                                                                 v1)
                                                                                                                              (coe
                                                                                                                                 ("inl"
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
                                                                                                                                       MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inl_1116)
                                                                                                                             else coe
                                                                                                                                    seq
                                                                                                                                    (coe
                                                                                                                                       v20)
                                                                                                                                    (let v21
                                                                                                                                           = coe
                                                                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                               erased
                                                                                                                                               (\ v21 ->
                                                                                                                                                  coe
                                                                                                                                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                    (coe
                                                                                                                                                       v1))
                                                                                                                                               (coe
                                                                                                                                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                  (coe
                                                                                                                                                     v1)
                                                                                                                                                  (coe
                                                                                                                                                     ("inr"
                                                                                                                                                      ::
                                                                                                                                                      Data.Text.Text))) in
                                                                                                                                     coe
                                                                                                                                       (case coe
                                                                                                                                               v21 of
                                                                                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v22 v23
                                                                                                                                            -> if coe
                                                                                                                                                    v22
                                                                                                                                                 then coe
                                                                                                                                                        seq
                                                                                                                                                        (coe
                                                                                                                                                           v23)
                                                                                                                                                        (coe
                                                                                                                                                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inr_1118)
                                                                                                                                                 else coe
                                                                                                                                                        seq
                                                                                                                                                        (coe
                                                                                                                                                           v23)
                                                                                                                                                        (coe
                                                                                                                                                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'other_1122)
                                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                      _ -> MAlonzo.RTE.mazUnreachableError)) in
                      coe
                        (case coe v6 of
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'id_1106
                             -> let v7
                                      = coe
                                          MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1854
                                          (coe v0) (coe ("id" :: Data.Text.Text))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_size_186
                                                (coe v0))
                                             (coe ("id" :: Data.Text.Text))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_named_188
                                                (coe v0))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190
                                                (coe v0)))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                                (coe v0))
                                             (coe ("id" :: Data.Text.Text))) in
                                coe
                                  (case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                       -> case coe v8 of
                                            MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v10 v11 v12 v13 v14
                                              -> let v15
                                                       = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__228
                                                           (coe v2) (coe v2) in
                                                 coe
                                                   (case coe v15 of
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                        -> if coe v16
                                                             then coe
                                                                    seq (coe v17)
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                       (coe v12)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          (coe v13)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe v14) erased)))
                                                             else coe
                                                                    seq (coe v17)
                                                                    (coe
                                                                       MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'fst_1108
                             -> let v7
                                      = coe
                                          MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1854
                                          (coe v0) (coe ("fst" :: Data.Text.Text))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_size_186
                                                (coe v0))
                                             (coe ("fst" :: Data.Text.Text))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_named_188
                                                (coe v0))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190
                                                (coe v0)))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                                (coe v0))
                                             (coe ("fst" :: Data.Text.Text))) in
                                coe
                                  (case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                       -> case coe v8 of
                                            MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v10 v11 v12 v13 v14
                                              -> let v15
                                                       = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__228
                                                           (coe v2) (coe v2) in
                                                 coe
                                                   (case coe v15 of
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                        -> if coe v16
                                                             then coe
                                                                    seq (coe v17)
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                       (coe v12)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          (coe v13)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe v14) erased)))
                                                             else coe
                                                                    seq (coe v17)
                                                                    (coe
                                                                       MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'snd_1110
                             -> let v7
                                      = coe
                                          MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1854
                                          (coe v0) (coe ("snd" :: Data.Text.Text))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_size_186
                                                (coe v0))
                                             (coe ("snd" :: Data.Text.Text))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_named_188
                                                (coe v0))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190
                                                (coe v0)))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                                (coe v0))
                                             (coe ("snd" :: Data.Text.Text))) in
                                coe
                                  (case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                       -> case coe v8 of
                                            MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v10 v11 v12 v13 v14
                                              -> let v15
                                                       = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__228
                                                           (coe v2) (coe v2) in
                                                 coe
                                                   (case coe v15 of
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                        -> if coe v16
                                                             then coe
                                                                    seq (coe v17)
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                       (coe v12)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          (coe v13)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe v14) erased)))
                                                             else coe
                                                                    seq (coe v17)
                                                                    (coe
                                                                       MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'terminal_1112
                             -> let v7
                                      = coe
                                          MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1854
                                          (coe v0) (coe ("terminal" :: Data.Text.Text))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_size_186
                                                (coe v0))
                                             (coe ("terminal" :: Data.Text.Text))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_named_188
                                                (coe v0))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190
                                                (coe v0)))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                                (coe v0))
                                             (coe ("terminal" :: Data.Text.Text))) in
                                coe
                                  (case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                       -> case coe v8 of
                                            MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v10 v11 v12 v13 v14
                                              -> let v15
                                                       = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__228
                                                           (coe v2) (coe v2) in
                                                 coe
                                                   (case coe v15 of
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                        -> if coe v16
                                                             then coe
                                                                    seq (coe v17)
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                       (coe v12)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          (coe v13)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe v14) erased)))
                                                             else coe
                                                                    seq (coe v17)
                                                                    (coe
                                                                       MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'initial_1114
                             -> let v7
                                      = coe
                                          MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1854
                                          (coe v0) (coe ("initial" :: Data.Text.Text))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_size_186
                                                (coe v0))
                                             (coe ("initial" :: Data.Text.Text))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_named_188
                                                (coe v0))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190
                                                (coe v0)))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                                (coe v0))
                                             (coe ("initial" :: Data.Text.Text))) in
                                coe
                                  (case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                       -> case coe v8 of
                                            MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v10 v11 v12 v13 v14
                                              -> let v15
                                                       = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__228
                                                           (coe v2) (coe v2) in
                                                 coe
                                                   (case coe v15 of
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                        -> if coe v16
                                                             then coe
                                                                    seq (coe v17)
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                       (coe v12)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          (coe v13)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe v14) erased)))
                                                             else coe
                                                                    seq (coe v17)
                                                                    (coe
                                                                       MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inl_1116
                             -> let v7
                                      = coe
                                          MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1854
                                          (coe v0) (coe ("inl" :: Data.Text.Text))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_size_186
                                                (coe v0))
                                             (coe ("inl" :: Data.Text.Text))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_named_188
                                                (coe v0))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190
                                                (coe v0)))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                                (coe v0))
                                             (coe ("inl" :: Data.Text.Text))) in
                                coe
                                  (case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                       -> case coe v8 of
                                            MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v10 v11 v12 v13 v14
                                              -> let v15
                                                       = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__228
                                                           (coe v2) (coe v2) in
                                                 coe
                                                   (case coe v15 of
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                        -> if coe v16
                                                             then coe
                                                                    seq (coe v17)
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                       (coe v12)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          (coe v13)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe v14) erased)))
                                                             else coe
                                                                    seq (coe v17)
                                                                    (coe
                                                                       MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inr_1118
                             -> let v7
                                      = coe
                                          MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1854
                                          (coe v0) (coe ("inr" :: Data.Text.Text))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_size_186
                                                (coe v0))
                                             (coe ("inr" :: Data.Text.Text))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_named_188
                                                (coe v0))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190
                                                (coe v0)))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                                (coe v0))
                                             (coe ("inr" :: Data.Text.Text))) in
                                coe
                                  (case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                       -> case coe v8 of
                                            MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v10 v11 v12 v13 v14
                                              -> let v15
                                                       = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__228
                                                           (coe v2) (coe v2) in
                                                 coe
                                                   (case coe v15 of
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                        -> if coe v16
                                                             then coe
                                                                    seq (coe v17)
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                       (coe v12)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          (coe v13)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe v14) erased)))
                                                             else coe
                                                                    seq (coe v17)
                                                                    (coe
                                                                       MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'other_1122
                             -> let v8
                                      = coe
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                          erased
                                          (\ v8 ->
                                             coe
                                               MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                               (coe v1))
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                                             (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                v1)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                ("unit" :: Data.Text.Text))) in
                                coe
                                  (case coe v8 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                       -> if coe v9
                                            then let v11
                                                       = seq
                                                           (coe v10)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe
                                                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304
                                                                 (coe
                                                                    MAlonzo.Code.Once.Type.C_Unit_122)
                                                                 (coe
                                                                    MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_70
                                                                    (coe
                                                                       MAlonzo.Code.Once.TypeCheck.Classify.d_size_186
                                                                       (coe v0)))
                                                                 (coe
                                                                    MAlonzo.Code.Once.Surface.Syntax.C_unit_328)
                                                                 (coe (0 :: Integer))
                                                                 (coe
                                                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                                    (coe v0)))
                                                              (coe
                                                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_44)) in
                                                 coe
                                                   (case coe v11 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                        -> case coe v12 of
                                                             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v14 v15 v16 v17 v18
                                                               -> let v19
                                                                        = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__228
                                                                            (coe v2) (coe v2) in
                                                                  coe
                                                                    (case coe v19 of
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                         -> if coe v20
                                                                              then coe
                                                                                     seq (coe v21)
                                                                                     (coe
                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                        (coe v16)
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                           (coe v17)
                                                                                           (coe
                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                              (coe
                                                                                                 v18)
                                                                                              erased)))
                                                                              else coe
                                                                                     seq (coe v21)
                                                                                     (coe
                                                                                        MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                                       _ -> MAlonzo.RTE.mazUnreachableError)
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                            else (let v11
                                                        = seq
                                                            (coe v10)
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1854
                                                               (coe v0) (coe v1)
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal_404
                                                                  (coe v0) (coe v1))
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                                                  (coe
                                                                     MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                                                     (coe v0))
                                                                  (coe v1))) in
                                                  coe
                                                    (case coe v11 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                         -> case coe v12 of
                                                              MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v14 v15 v16 v17 v18
                                                                -> let v19
                                                                         = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__228
                                                                             (coe v2) (coe v2) in
                                                                   coe
                                                                     (case coe v19 of
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                          -> if coe v20
                                                                               then coe
                                                                                      seq (coe v21)
                                                                                      (coe
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                         (coe v16)
                                                                                         (coe
                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                            (coe
                                                                                               v17)
                                                                                            (coe
                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                               (coe
                                                                                                  v18)
                                                                                               erased)))
                                                                               else coe
                                                                                      seq (coe v21)
                                                                                      (coe
                                                                                         MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.completeness-gap-inl-app-check-eq
d_completeness'45'gap'45'inl'45'app'45'check'45'eq_2382 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_completeness'45'gap'45'inl'45'app'45'check'45'eq_2382 v0 v1 v2
                                                        ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_completeness'45'gap'45'inl'45'app'45'check'45'eq_2382 v0 v1 v2
du_completeness'45'gap'45'inl'45'app'45'check'45'eq_2382 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_completeness'45'gap'45'inl'45'app'45'check'45'eq_2382 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_1666
              (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_328 v6 v7 v8 v9
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_546 v6 v2
                          (coe
                             MAlonzo.Code.Once.IR.C_inl_56 (coe MAlonzo.Code.Once.IR.C_Heap_8))
                          v7)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe addInt (coe (1 :: Integer)) (coe v8))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.completeness-gap-inr-app-check-eq
d_completeness'45'gap'45'inr'45'app'45'check'45'eq_2430 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_completeness'45'gap'45'inr'45'app'45'check'45'eq_2430 v0 v1 ~v2
                                                        v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_completeness'45'gap'45'inr'45'app'45'check'45'eq_2430 v0 v1 v3
du_completeness'45'gap'45'inr'45'app'45'check'45'eq_2430 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_completeness'45'gap'45'inr'45'app'45'check'45'eq_2430 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_1666
              (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_328 v6 v7 v8 v9
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_546 v6 v2
                          (coe
                             MAlonzo.Code.Once.IR.C_inr_62 (coe MAlonzo.Code.Once.IR.C_Heap_8))
                          v7)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe addInt (coe (1 :: Integer)) (coe v8))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.completeness-gap-initial-app-check-eq
d_completeness'45'gap'45'initial'45'app'45'check'45'eq_2476 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_completeness'45'gap'45'initial'45'app'45'check'45'eq_2476 v0 v1
                                                            ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_completeness'45'gap'45'initial'45'app'45'check'45'eq_2476
      v0 v1
du_completeness'45'gap'45'initial'45'app'45'check'45'eq_2476 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_completeness'45'gap'45'initial'45'app'45'check'45'eq_2476 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_1666
              (coe v0) (coe v1) (coe MAlonzo.Code.Once.Type.C_Void_124) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_328 v5 v6 v7 v8
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_546 v5
                          (coe MAlonzo.Code.Once.Type.C_Void_124)
                          (coe MAlonzo.Code.Once.IR.C_initial_78) v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe addInt (coe (1 :: Integer)) (coe v7))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8) erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.embedOrSubsume-lifts
d_embedOrSubsume'45'lifts_2522 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_embedOrSubsume'45'lifts_2522 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_embedOrSubsume'45'lifts_2522 v2 v3 v4
du_embedOrSubsume'45'lifts_2522 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_embedOrSubsume'45'lifts_2522 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_304 v5 v6 v7 v8 v9
               -> let v10
                        = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__228
                            (coe
                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v0)
                               (coe
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                                  (coe MAlonzo.Code.Once.Type.C_pure_34))
                               (coe v1))
                            (coe v5) in
                  coe
                    (case coe v10 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                         -> coe
                              seq (coe v11)
                              (coe
                                 seq (coe v12)
                                 (let v13
                                        = coe
                                            MAlonzo.Code.Once.TypeCheck.Elaborate.du_'8799'T'45''8658''45'aux_116
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__228
                                               (coe v0) (coe v0))
                                            (coe
                                               MAlonzo.Code.Once.Type.d__'8799'k__100
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                  (coe MAlonzo.Code.Once.Type.C_eff_36))
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                  (coe MAlonzo.Code.Once.Type.C_pure_34)))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__228
                                               (coe v1) (coe v1)) in
                                  coe
                                    (case coe v13 of
                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                         -> coe
                                              seq (coe v14)
                                              (case coe v15 of
                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                   -> let v17
                                                            = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__228
                                                                (coe v0) (coe v0) in
                                                      coe
                                                        (let v18
                                                               = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__228
                                                                   (coe v1) (coe v1) in
                                                         coe
                                                           (case coe v17 of
                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v19 v20
                                                                -> if coe v19
                                                                     then coe
                                                                            seq (coe v20)
                                                                            (case coe v18 of
                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                                                 -> if coe v21
                                                                                      then case coe
                                                                                                  v22 of
                                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v23
                                                                                               -> coe
                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Once.Surface.Syntax.C_arr''_496
                                                                                                       v7)
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                       (coe
                                                                                                          v8)
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                          (coe
                                                                                                             v9)
                                                                                                          erased))
                                                                                             _ -> coe
                                                                                                    seq
                                                                                                    (coe
                                                                                                       v21)
                                                                                                    (coe
                                                                                                       seq
                                                                                                       (coe
                                                                                                          v22)
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
                                                                                      else (case coe
                                                                                                   v22 of
                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                                -> coe
                                                                                                     MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                                              _ -> coe
                                                                                                     seq
                                                                                                     (coe
                                                                                                        v21)
                                                                                                     (coe
                                                                                                        seq
                                                                                                        (coe
                                                                                                           v22)
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)))
                                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                                     else coe
                                                                            seq (coe v20)
                                                                            (coe
                                                                               MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.completeness-gap-arg-driven-app-check
d_completeness'45'gap'45'arg'45'driven'45'app'45'check_3002
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.Completeness.completeness-gap-arg-driven-app-check"
-- Once.TypeCheck.Completeness.completeness-gap-arg-driven-app-check-eff
d_completeness'45'gap'45'arg'45'driven'45'app'45'check'45'eff_3026
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.Completeness.completeness-gap-arg-driven-app-check-eff"
-- Once.TypeCheck.Completeness.regrade-eff
d_regrade'45'eff_3038 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  Maybe
    MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18
d_regrade'45'eff_3038 ~v0 v1 v2 v3 ~v4 v5
  = du_regrade'45'eff_3038 v1 v2 v3 v5
du_regrade'45'eff_3038 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  Maybe
    MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18
du_regrade'45'eff_3038 v0 v1 v2 v3
  = let v4 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'id_344
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'id_344)
         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'fst_354
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'42'__126 v11 v12
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'fst_354)
                _ -> coe v4
         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'snd_364
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'42'__126 v11 v12
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'snd_364)
                _ -> coe v4
         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'terminal_372
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'terminal_372)
         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'initial_380
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'initial_380)
         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inl_390
           -> case coe v2 of
                MAlonzo.Code.Once.Type.C__'43'__128 v11 v12
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inl_390)
                _ -> coe v4
         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inr_400
           -> case coe v2 of
                MAlonzo.Code.Once.Type.C__'43'__128 v11 v12
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inr_400)
                _ -> coe v4
         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'compose_416 v9 v13 v14
           -> case coe v0 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
                  -> case coe v15 of
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
                         -> let v19
                                  = coe
                                      du_regrade'45'eff_3038 (coe v18) (coe v9) (coe v2)
                                      (coe v13) in
                            coe
                              (let v20
                                     = coe
                                         du_regrade'45'eff_3038 (coe v16) (coe v1) (coe v9)
                                         (coe v14) in
                               coe
                                 (case coe v19 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v21
                                      -> case coe v20 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v22
                                             -> coe
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'compose_416
                                                     v9 v21 v22)
                                           _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                    _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                       _ -> coe v4
                _ -> coe v4
         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'case_432 v12 v13
           -> case coe v0 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
                  -> case coe v14 of
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
                         -> case coe v1 of
                              MAlonzo.Code.Once.Type.C__'43'__128 v18 v19
                                -> let v20
                                         = coe
                                             du_regrade'45'eff_3038 (coe v17) (coe v18) (coe v2)
                                             (coe v12) in
                                   coe
                                     (let v21
                                            = coe
                                                du_regrade'45'eff_3038 (coe v15) (coe v19) (coe v2)
                                                (coe v13) in
                                      coe
                                        (case coe v20 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v22
                                             -> case coe v21 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v23
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'case_432
                                                            v22 v23)
                                                  _ -> coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                           _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                              _ -> coe v4
                       _ -> coe v4
                _ -> coe v4
         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_484 v10
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_484 v10)
         _ -> coe v4)
-- Once.TypeCheck.Completeness.just≢nothing
d_just'8802'nothing_3120 ::
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_just'8802'nothing_3120 = erased
-- Once.TypeCheck.Completeness.StrongElab
d_StrongElab_3132 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 -> ()
d_StrongElab_3132 = erased
-- Once.TypeCheck.Completeness.go-canonical
d_go'45'canonical_3172 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go'45'canonical_3172 = erased
-- Once.TypeCheck.Completeness.composeGo-success
d_composeGo'45'success_3220 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_composeGo'45'success_3220 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 ~v9
                            ~v10 ~v11 ~v12 ~v13 ~v14 v15 v16 v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23
                            ~v24 ~v25
  = du_composeGo'45'success_3220 v6 v7 v8 v15 v16 v17
du_composeGo'45'success_3220 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_composeGo'45'success_3220 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.IR.C__'8728'__30 v0 v1 v2)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            addInt (coe (1 :: Integer))
            (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v3) (coe v5)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
            (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)))
-- Once.TypeCheck.Completeness.cgo-usage
d_cgo'45'usage_3286 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cgo'45'usage_3286 = erased
-- Once.TypeCheck.Completeness.ccgo-usage
d_ccgo'45'usage_3652 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ccgo'45'usage_3652 = erased
-- Once.TypeCheck.Completeness.ccatago-usage
d_ccatago'45'usage_4018 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ccatago'45'usage_4018 = erased
-- Once.TypeCheck.Completeness.named-morph-strong
d_named'45'morph'45'strong_4128
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.Completeness.named-morph-strong"
-- Once.TypeCheck.Completeness.named-morph-strong-resolved
d_named'45'morph'45'strong'45'resolved_4140
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.Completeness.named-morph-strong-resolved"
-- Once.TypeCheck.Completeness.checkG-realize
d_checkG'45'realize_4154 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkG'45'realize_4154 = erased
-- Once.TypeCheck.Completeness.morph-elab
d_morph'45'elab_4492 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_morph'45'elab_4492 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'id_344
        -> let v11
                 = coe
                     MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1854
                     (coe v0) (coe ("id" :: Data.Text.Text))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                        (coe ("id" :: Data.Text.Text))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190 (coe v0)))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194 (coe v0))
                        (coe ("id" :: Data.Text.Text))) in
           coe
             (case coe v11 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                  -> coe
                       seq (coe v12)
                       (let v14
                              = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                                  (coe ("id" :: Data.Text.Text))
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190
                                     (coe v0)) in
                        coe
                          (case coe v14 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                               -> case coe v15 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                      -> coe
                                           seq (coe v17)
                                           (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                               -> let v15
                                        = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                               (coe v0))
                                            (coe ("id" :: Data.Text.Text)) in
                                  coe
                                    (case coe v15 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                         -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> let v16
                                                  = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__228
                                                      (coe v2) (coe v2) in
                                            coe
                                              (case coe v16 of
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                   -> if coe v17
                                                        then coe
                                                               seq (coe v18)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe MAlonzo.Code.Once.IR.C_id_22)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                     (coe
                                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'id_344)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                        (coe
                                                                           MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                           (coe
                                                                              MAlonzo.Code.Once.IR.C_id_22))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe (0 :: Integer))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                              (coe
                                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                                                 (coe v0))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_520
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'id_344))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    erased
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       erased
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                          erased
                                                                                          erased)))))))))
                                                        else coe
                                                               seq (coe v18)
                                                               (coe
                                                                  MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                             _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'fst_354
        -> let v12
                 = coe
                     MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1854
                     (coe v0) (coe ("fst" :: Data.Text.Text))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                        (coe ("fst" :: Data.Text.Text))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190 (coe v0)))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194 (coe v0))
                        (coe ("fst" :: Data.Text.Text))) in
           coe
             (case coe v12 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                  -> coe
                       seq (coe v13)
                       (let v15
                              = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                                  (coe ("fst" :: Data.Text.Text))
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190
                                     (coe v0)) in
                        coe
                          (case coe v15 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                               -> case coe v16 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                      -> coe
                                           seq (coe v18)
                                           (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                               -> let v16
                                        = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                               (coe v0))
                                            (coe ("fst" :: Data.Text.Text)) in
                                  coe
                                    (case coe v16 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                         -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> let v17
                                                  = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__228
                                                      (coe v3) (coe v3) in
                                            coe
                                              (case coe v17 of
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                   -> if coe v18
                                                        then coe
                                                               seq (coe v19)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe
                                                                     MAlonzo.Code.Once.IR.C_fst_44)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                     (coe
                                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'fst_354)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                        (coe
                                                                           MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                           (coe
                                                                              MAlonzo.Code.Once.IR.C_fst_44))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe (0 :: Integer))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                              (coe
                                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                                                 (coe v0))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_520
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'fst_354))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    erased
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       erased
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                          erased
                                                                                          erased)))))))))
                                                        else coe
                                                               seq (coe v19)
                                                               (coe
                                                                  MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                             _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'snd_364
        -> let v12
                 = coe
                     MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1854
                     (coe v0) (coe ("snd" :: Data.Text.Text))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                        (coe ("snd" :: Data.Text.Text))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190 (coe v0)))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194 (coe v0))
                        (coe ("snd" :: Data.Text.Text))) in
           coe
             (case coe v12 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                  -> coe
                       seq (coe v13)
                       (let v15
                              = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                                  (coe ("snd" :: Data.Text.Text))
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190
                                     (coe v0)) in
                        coe
                          (case coe v15 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                               -> case coe v16 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                      -> coe
                                           seq (coe v18)
                                           (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                               -> let v16
                                        = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                               (coe v0))
                                            (coe ("snd" :: Data.Text.Text)) in
                                  coe
                                    (case coe v16 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                         -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> let v17
                                                  = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__228
                                                      (coe v3) (coe v3) in
                                            coe
                                              (case coe v17 of
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                   -> if coe v18
                                                        then coe
                                                               seq (coe v19)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe
                                                                     MAlonzo.Code.Once.IR.C_snd_50)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                     (coe
                                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'snd_364)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                        (coe
                                                                           MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                           (coe
                                                                              MAlonzo.Code.Once.IR.C_snd_50))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe (0 :: Integer))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                              (coe
                                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                                                 (coe v0))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_520
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'snd_364))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    erased
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       erased
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                          erased
                                                                                          erased)))))))))
                                                        else coe
                                                               seq (coe v19)
                                                               (coe
                                                                  MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                             _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'terminal_372
        -> let v11
                 = coe
                     MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1854
                     (coe v0) (coe ("terminal" :: Data.Text.Text))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                        (coe ("terminal" :: Data.Text.Text))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190 (coe v0)))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194 (coe v0))
                        (coe ("terminal" :: Data.Text.Text))) in
           coe
             (case coe v11 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                  -> coe
                       seq (coe v12)
                       (let v14
                              = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                                  (coe ("terminal" :: Data.Text.Text))
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190
                                     (coe v0)) in
                        coe
                          (case coe v14 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                               -> case coe v15 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                      -> coe
                                           seq (coe v17)
                                           (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                               -> let v15
                                        = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                               (coe v0))
                                            (coe ("terminal" :: Data.Text.Text)) in
                                  coe
                                    (case coe v15 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                         -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                              (coe MAlonzo.Code.Once.IR.C_terminal_74)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe
                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'terminal_372)
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe
                                                       MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                       (coe MAlonzo.Code.Once.IR.C_terminal_74))
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe (0 :: Integer))
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                             (coe v0))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_520
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'terminal_372))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                erased
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   erased
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      erased erased))))))))
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                             _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'initial_380
        -> let v11
                 = coe
                     MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1854
                     (coe v0) (coe ("initial" :: Data.Text.Text))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                        (coe ("initial" :: Data.Text.Text))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190 (coe v0)))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194 (coe v0))
                        (coe ("initial" :: Data.Text.Text))) in
           coe
             (case coe v11 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                  -> coe
                       seq (coe v12)
                       (let v14
                              = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                                  (coe ("initial" :: Data.Text.Text))
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190
                                     (coe v0)) in
                        coe
                          (case coe v14 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                               -> case coe v15 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                      -> coe
                                           seq (coe v17)
                                           (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                               -> let v15
                                        = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                               (coe v0))
                                            (coe ("initial" :: Data.Text.Text)) in
                                  coe
                                    (case coe v15 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                         -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                              (coe MAlonzo.Code.Once.IR.C_initial_78)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe
                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'initial_380)
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe
                                                       MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                       (coe MAlonzo.Code.Once.IR.C_initial_78))
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe (0 :: Integer))
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                             (coe v0))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_520
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'initial_380))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                erased
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   erased
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      erased erased))))))))
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                             _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inl_390
        -> let v12
                 = coe
                     MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1854
                     (coe v0) (coe ("inl" :: Data.Text.Text))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                        (coe ("inl" :: Data.Text.Text))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190 (coe v0)))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194 (coe v0))
                        (coe ("inl" :: Data.Text.Text))) in
           coe
             (case coe v12 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                  -> coe
                       seq (coe v13)
                       (let v15
                              = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                                  (coe ("inl" :: Data.Text.Text))
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190
                                     (coe v0)) in
                        coe
                          (case coe v15 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                               -> case coe v16 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                      -> coe
                                           seq (coe v18)
                                           (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                               -> let v16
                                        = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                               (coe v0))
                                            (coe ("inl" :: Data.Text.Text)) in
                                  coe
                                    (case coe v16 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                         -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> let v17
                                                  = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__228
                                                      (coe v2) (coe v2) in
                                            coe
                                              (case coe v17 of
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                   -> if coe v18
                                                        then coe
                                                               seq (coe v19)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe
                                                                     MAlonzo.Code.Once.IR.C_inl_56
                                                                     (coe
                                                                        MAlonzo.Code.Once.IR.C_Heap_8))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                     (coe
                                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inl_390)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                        (coe
                                                                           MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                           (coe
                                                                              MAlonzo.Code.Once.IR.C_inl_56
                                                                              (coe
                                                                                 MAlonzo.Code.Once.IR.C_Heap_8)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe (0 :: Integer))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                              (coe
                                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                                                 (coe v0))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_520
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inl_390))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    erased
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       erased
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                          erased
                                                                                          erased)))))))))
                                                        else coe
                                                               seq (coe v19)
                                                               (coe
                                                                  MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                             _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inr_400
        -> let v12
                 = coe
                     MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1854
                     (coe v0) (coe ("inr" :: Data.Text.Text))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                        (coe ("inr" :: Data.Text.Text))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190 (coe v0)))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194 (coe v0))
                        (coe ("inr" :: Data.Text.Text))) in
           coe
             (case coe v12 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                  -> coe
                       seq (coe v13)
                       (let v15
                              = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                                  (coe ("inr" :: Data.Text.Text))
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190
                                     (coe v0)) in
                        coe
                          (case coe v15 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                               -> case coe v16 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                      -> coe
                                           seq (coe v18)
                                           (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                               -> let v16
                                        = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                               (coe v0))
                                            (coe ("inr" :: Data.Text.Text)) in
                                  coe
                                    (case coe v16 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                         -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> let v17
                                                  = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__228
                                                      (coe v2) (coe v2) in
                                            coe
                                              (case coe v17 of
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                   -> if coe v18
                                                        then coe
                                                               seq (coe v19)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe
                                                                     MAlonzo.Code.Once.IR.C_inr_62
                                                                     (coe
                                                                        MAlonzo.Code.Once.IR.C_Heap_8))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                     (coe
                                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inr_400)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                        (coe
                                                                           MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                           (coe
                                                                              MAlonzo.Code.Once.IR.C_inr_62
                                                                              (coe
                                                                                 MAlonzo.Code.Once.IR.C_Heap_8)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe (0 :: Integer))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                              (coe
                                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                                                 (coe v0))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_520
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inr_400))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    erased
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       erased
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                          erased
                                                                                          erased)))))))))
                                                        else coe
                                                               seq (coe v19)
                                                               (coe
                                                                  MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                             _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'compose_416 v10 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
                      -> case coe v4 of
                           MAlonzo.Code.Once.Type.C_pure_34
                             -> let v20
                                      = d_morph'45'elab_4492
                                          (coe v0) (coe v19) (coe v10) (coe v3) (coe v4)
                                          (coe v14) in
                                coe
                                  (let v21
                                         = d_morph'45'elab_4492
                                             (coe v0) (coe v17) (coe v2) (coe v10) (coe v4)
                                             (coe v15) in
                                   coe
                                     (case coe v20 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                          -> case coe v23 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                 -> case coe v25 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                        -> case coe v27 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                                               -> case coe v29 of
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                                                      -> case coe v31 of
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                                                             -> case coe v33 of
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                                                                                    -> case coe
                                                                                              v35 of
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
                                                                                           -> coe
                                                                                                seq
                                                                                                (coe
                                                                                                   v37)
                                                                                                (case coe
                                                                                                        v21 of
                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v38 v39
                                                                                                     -> case coe
                                                                                                               v39 of
                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v40 v41
                                                                                                            -> case coe
                                                                                                                      v41 of
                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v42 v43
                                                                                                                   -> case coe
                                                                                                                             v43 of
                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v44 v45
                                                                                                                          -> case coe
                                                                                                                                    v45 of
                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v46 v47
                                                                                                                                 -> case coe
                                                                                                                                           v47 of
                                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v48 v49
                                                                                                                                        -> case coe
                                                                                                                                                  v49 of
                                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v50 v51
                                                                                                                                               -> case coe
                                                                                                                                                         v51 of
                                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v52 v53
                                                                                                                                                      -> coe
                                                                                                                                                           seq
                                                                                                                                                           (coe
                                                                                                                                                              v53)
                                                                                                                                                           (coe
                                                                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                              (coe
                                                                                                                                                                 MAlonzo.Code.Once.IR.C__'8728'__30
                                                                                                                                                                 v10
                                                                                                                                                                 v22
                                                                                                                                                                 v38)
                                                                                                                                                              (coe
                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                 (coe
                                                                                                                                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'compose_416
                                                                                                                                                                    v10
                                                                                                                                                                    v24
                                                                                                                                                                    v40)
                                                                                                                                                                 (coe
                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                    (coe
                                                                                                                                                                       MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                                                                                                                       (coe
                                                                                                                                                                          MAlonzo.Code.Once.IR.C__'8728'__30
                                                                                                                                                                          v10
                                                                                                                                                                          v22
                                                                                                                                                                          v38))
                                                                                                                                                                    (coe
                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                       (coe
                                                                                                                                                                          addInt
                                                                                                                                                                          (coe
                                                                                                                                                                             (1 ::
                                                                                                                                                                                Integer))
                                                                                                                                                                          (coe
                                                                                                                                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                                                                                             (coe
                                                                                                                                                                                v28)
                                                                                                                                                                             (coe
                                                                                                                                                                                v44)))
                                                                                                                                                                       (coe
                                                                                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                          (coe
                                                                                                                                                                             v30)
                                                                                                                                                                          (coe
                                                                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                             (coe
                                                                                                                                                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_520
                                                                                                                                                                                (coe
                                                                                                                                                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'compose_416
                                                                                                                                                                                   v10
                                                                                                                                                                                   v24
                                                                                                                                                                                   v40))
                                                                                                                                                                             (coe
                                                                                                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                erased
                                                                                                                                                                                (coe
                                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                   erased
                                                                                                                                                                                   (coe
                                                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                      erased
                                                                                                                                                                                      erased)))))))))
                                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                           MAlonzo.Code.Once.Type.C_eff_36
                             -> let v20
                                      = d_morph'45'elab_4492
                                          (coe v0) (coe v19) (coe v10) (coe v3) (coe v4)
                                          (coe v14) in
                                coe
                                  (let v21
                                         = d_morph'45'elab_4492
                                             (coe v0) (coe v17) (coe v2) (coe v10) (coe v4)
                                             (coe v15) in
                                   coe
                                     (case coe v20 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                          -> case coe v23 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                 -> case coe v25 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                        -> case coe v27 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                                               -> case coe v29 of
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                                                      -> case coe v31 of
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                                                             -> case coe v33 of
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                                                                                    -> case coe
                                                                                              v35 of
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
                                                                                           -> coe
                                                                                                seq
                                                                                                (coe
                                                                                                   v37)
                                                                                                (case coe
                                                                                                        v21 of
                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v38 v39
                                                                                                     -> case coe
                                                                                                               v39 of
                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v40 v41
                                                                                                            -> case coe
                                                                                                                      v41 of
                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v42 v43
                                                                                                                   -> case coe
                                                                                                                             v43 of
                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v44 v45
                                                                                                                          -> case coe
                                                                                                                                    v45 of
                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v46 v47
                                                                                                                                 -> case coe
                                                                                                                                           v47 of
                                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v48 v49
                                                                                                                                        -> case coe
                                                                                                                                                  v49 of
                                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v50 v51
                                                                                                                                               -> case coe
                                                                                                                                                         v51 of
                                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v52 v53
                                                                                                                                                      -> coe
                                                                                                                                                           seq
                                                                                                                                                           (coe
                                                                                                                                                              v53)
                                                                                                                                                           (coe
                                                                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                              (coe
                                                                                                                                                                 MAlonzo.Code.Once.IR.C__'8728'__30
                                                                                                                                                                 v10
                                                                                                                                                                 v22
                                                                                                                                                                 v38)
                                                                                                                                                              (coe
                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                 (coe
                                                                                                                                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'compose_416
                                                                                                                                                                    v10
                                                                                                                                                                    v24
                                                                                                                                                                    v40)
                                                                                                                                                                 (coe
                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                    (coe
                                                                                                                                                                       MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                                                                                                                       (coe
                                                                                                                                                                          MAlonzo.Code.Once.IR.C__'8728'__30
                                                                                                                                                                          v10
                                                                                                                                                                          v22
                                                                                                                                                                          v38))
                                                                                                                                                                    (coe
                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                       (coe
                                                                                                                                                                          addInt
                                                                                                                                                                          (coe
                                                                                                                                                                             (1 ::
                                                                                                                                                                                Integer))
                                                                                                                                                                          (coe
                                                                                                                                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                                                                                             (coe
                                                                                                                                                                                v28)
                                                                                                                                                                             (coe
                                                                                                                                                                                v44)))
                                                                                                                                                                       (coe
                                                                                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                          (coe
                                                                                                                                                                             v30)
                                                                                                                                                                          (coe
                                                                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                             (coe
                                                                                                                                                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_520
                                                                                                                                                                                (coe
                                                                                                                                                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'compose_416
                                                                                                                                                                                   v10
                                                                                                                                                                                   v24
                                                                                                                                                                                   v40))
                                                                                                                                                                             (coe
                                                                                                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                erased
                                                                                                                                                                                (coe
                                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                   erased
                                                                                                                                                                                   (coe
                                                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                      erased
                                                                                                                                                                                      erased)))))))))
                                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'case_432 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'43'__128 v19 v20
                             -> case coe v4 of
                                  MAlonzo.Code.Once.Type.C_pure_34
                                    -> let v21
                                             = d_morph'45'elab_4492
                                                 (coe v0) (coe v18) (coe v19) (coe v3) (coe v4)
                                                 (coe v13) in
                                       coe
                                         (let v22
                                                = d_morph'45'elab_4492
                                                    (coe v0) (coe v16) (coe v20) (coe v3) (coe v4)
                                                    (coe v14) in
                                          coe
                                            (case coe v21 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                                 -> case coe v24 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                                        -> case coe v26 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                                               -> case coe v28 of
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v29 v30
                                                                      -> case coe v30 of
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v31 v32
                                                                             -> case coe v32 of
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v33 v34
                                                                                    -> case coe
                                                                                              v34 of
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v35 v36
                                                                                           -> case coe
                                                                                                     v36 of
                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v37 v38
                                                                                                  -> coe
                                                                                                       seq
                                                                                                       (coe
                                                                                                          v38)
                                                                                                       (case coe
                                                                                                               v22 of
                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v39 v40
                                                                                                            -> case coe
                                                                                                                      v40 of
                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v41 v42
                                                                                                                   -> case coe
                                                                                                                             v42 of
                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v43 v44
                                                                                                                          -> case coe
                                                                                                                                    v44 of
                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v45 v46
                                                                                                                                 -> case coe
                                                                                                                                           v46 of
                                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v47 v48
                                                                                                                                        -> case coe
                                                                                                                                                  v48 of
                                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v49 v50
                                                                                                                                               -> case coe
                                                                                                                                                         v50 of
                                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v51 v52
                                                                                                                                                      -> case coe
                                                                                                                                                                v52 of
                                                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v53 v54
                                                                                                                                                             -> coe
                                                                                                                                                                  seq
                                                                                                                                                                  (coe
                                                                                                                                                                     v54)
                                                                                                                                                                  (coe
                                                                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                     (coe
                                                                                                                                                                        MAlonzo.Code.Once.IR.C_case_70
                                                                                                                                                                        v23
                                                                                                                                                                        v39)
                                                                                                                                                                     (coe
                                                                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                        (coe
                                                                                                                                                                           MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'case_432
                                                                                                                                                                           v25
                                                                                                                                                                           v41)
                                                                                                                                                                        (coe
                                                                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                           (coe
                                                                                                                                                                              MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                                                                                                                              (coe
                                                                                                                                                                                 MAlonzo.Code.Once.IR.C_case_70
                                                                                                                                                                                 v23
                                                                                                                                                                                 v39))
                                                                                                                                                                           (coe
                                                                                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                              (coe
                                                                                                                                                                                 addInt
                                                                                                                                                                                 (coe
                                                                                                                                                                                    (1 ::
                                                                                                                                                                                       Integer))
                                                                                                                                                                                 (coe
                                                                                                                                                                                    MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                                                                                                    (coe
                                                                                                                                                                                       v29)
                                                                                                                                                                                    (coe
                                                                                                                                                                                       v45)))
                                                                                                                                                                              (coe
                                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                 (coe
                                                                                                                                                                                    v31)
                                                                                                                                                                                 (coe
                                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                    (coe
                                                                                                                                                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_520
                                                                                                                                                                                       (coe
                                                                                                                                                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'case_432
                                                                                                                                                                                          v25
                                                                                                                                                                                          v41))
                                                                                                                                                                                    (coe
                                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                       erased
                                                                                                                                                                                       (coe
                                                                                                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                          erased
                                                                                                                                                                                          (coe
                                                                                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                             erased
                                                                                                                                                                                             erased)))))))))
                                                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                  MAlonzo.Code.Once.Type.C_eff_36
                                    -> let v21
                                             = d_morph'45'elab_4492
                                                 (coe v0) (coe v18) (coe v19) (coe v3) (coe v4)
                                                 (coe v13) in
                                       coe
                                         (let v22
                                                = d_morph'45'elab_4492
                                                    (coe v0) (coe v16) (coe v20) (coe v3) (coe v4)
                                                    (coe v14) in
                                          coe
                                            (case coe v21 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                                 -> case coe v24 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                                        -> case coe v26 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                                               -> case coe v28 of
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v29 v30
                                                                      -> case coe v30 of
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v31 v32
                                                                             -> case coe v32 of
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v33 v34
                                                                                    -> case coe
                                                                                              v34 of
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v35 v36
                                                                                           -> case coe
                                                                                                     v36 of
                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v37 v38
                                                                                                  -> coe
                                                                                                       seq
                                                                                                       (coe
                                                                                                          v38)
                                                                                                       (case coe
                                                                                                               v22 of
                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v39 v40
                                                                                                            -> case coe
                                                                                                                      v40 of
                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v41 v42
                                                                                                                   -> case coe
                                                                                                                             v42 of
                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v43 v44
                                                                                                                          -> case coe
                                                                                                                                    v44 of
                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v45 v46
                                                                                                                                 -> case coe
                                                                                                                                           v46 of
                                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v47 v48
                                                                                                                                        -> case coe
                                                                                                                                                  v48 of
                                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v49 v50
                                                                                                                                               -> case coe
                                                                                                                                                         v50 of
                                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v51 v52
                                                                                                                                                      -> case coe
                                                                                                                                                                v52 of
                                                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v53 v54
                                                                                                                                                             -> coe
                                                                                                                                                                  seq
                                                                                                                                                                  (coe
                                                                                                                                                                     v54)
                                                                                                                                                                  (coe
                                                                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                     (coe
                                                                                                                                                                        MAlonzo.Code.Once.IR.C_case_70
                                                                                                                                                                        v23
                                                                                                                                                                        v39)
                                                                                                                                                                     (coe
                                                                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                        (coe
                                                                                                                                                                           MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'case_432
                                                                                                                                                                           v25
                                                                                                                                                                           v41)
                                                                                                                                                                        (coe
                                                                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                           (coe
                                                                                                                                                                              MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                                                                                                                              (coe
                                                                                                                                                                                 MAlonzo.Code.Once.IR.C_case_70
                                                                                                                                                                                 v23
                                                                                                                                                                                 v39))
                                                                                                                                                                           (coe
                                                                                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                              (coe
                                                                                                                                                                                 addInt
                                                                                                                                                                                 (coe
                                                                                                                                                                                    (1 ::
                                                                                                                                                                                       Integer))
                                                                                                                                                                                 (coe
                                                                                                                                                                                    MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                                                                                                    (coe
                                                                                                                                                                                       v29)
                                                                                                                                                                                    (coe
                                                                                                                                                                                       v45)))
                                                                                                                                                                              (coe
                                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                 (coe
                                                                                                                                                                                    v31)
                                                                                                                                                                                 (coe
                                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                    (coe
                                                                                                                                                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_520
                                                                                                                                                                                       (coe
                                                                                                                                                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'case_432
                                                                                                                                                                                          v25
                                                                                                                                                                                          v41))
                                                                                                                                                                                    (coe
                                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                       erased
                                                                                                                                                                                       (coe
                                                                                                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                          erased
                                                                                                                                                                                          (coe
                                                                                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                             erased
                                                                                                                                                                                             erased)))))))))
                                                                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'pair_446 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> case coe v14 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
                      -> case coe v3 of
                           MAlonzo.Code.Once.Type.C__'42'__126 v18 v19
                             -> let v20
                                      = d_morph'45'elab_4492
                                          (coe v0) (coe v17) (coe v2) (coe v18)
                                          (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v12) in
                                coe
                                  (let v21
                                         = d_morph'45'elab_4492
                                             (coe v0) (coe v15) (coe v2) (coe v19)
                                             (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v13) in
                                   coe
                                     (case coe v20 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                          -> case coe v23 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                 -> case coe v25 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                        -> case coe v27 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                                               -> case coe v29 of
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                                                      -> case coe v31 of
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                                                             -> case coe v33 of
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                                                                                    -> case coe
                                                                                              v35 of
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
                                                                                           -> coe
                                                                                                seq
                                                                                                (coe
                                                                                                   v37)
                                                                                                (case coe
                                                                                                        v21 of
                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v38 v39
                                                                                                     -> case coe
                                                                                                               v39 of
                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v40 v41
                                                                                                            -> case coe
                                                                                                                      v41 of
                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v42 v43
                                                                                                                   -> case coe
                                                                                                                             v43 of
                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v44 v45
                                                                                                                          -> case coe
                                                                                                                                    v45 of
                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v46 v47
                                                                                                                                 -> case coe
                                                                                                                                           v47 of
                                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v48 v49
                                                                                                                                        -> case coe
                                                                                                                                                  v49 of
                                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v50 v51
                                                                                                                                               -> case coe
                                                                                                                                                         v51 of
                                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v52 v53
                                                                                                                                                      -> coe
                                                                                                                                                           seq
                                                                                                                                                           (coe
                                                                                                                                                              v53)
                                                                                                                                                           (coe
                                                                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                              (coe
                                                                                                                                                                 MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                                                                                                                                                                 v22
                                                                                                                                                                 v38
                                                                                                                                                                 (coe
                                                                                                                                                                    MAlonzo.Code.Once.IR.C_Heap_8))
                                                                                                                                                              (coe
                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                 (coe
                                                                                                                                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'pair_446
                                                                                                                                                                    v24
                                                                                                                                                                    v40)
                                                                                                                                                                 (coe
                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                    (coe
                                                                                                                                                                       MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                                                                                                                       (coe
                                                                                                                                                                          MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                                                                                                                                                                          v22
                                                                                                                                                                          v38
                                                                                                                                                                          (coe
                                                                                                                                                                             MAlonzo.Code.Once.IR.C_Heap_8)))
                                                                                                                                                                    (coe
                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                       (coe
                                                                                                                                                                          addInt
                                                                                                                                                                          (coe
                                                                                                                                                                             (1 ::
                                                                                                                                                                                Integer))
                                                                                                                                                                          (coe
                                                                                                                                                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                                                                                             (coe
                                                                                                                                                                                v28)
                                                                                                                                                                             (coe
                                                                                                                                                                                v44)))
                                                                                                                                                                       (coe
                                                                                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                          (coe
                                                                                                                                                                             v46)
                                                                                                                                                                          (coe
                                                                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                             (coe
                                                                                                                                                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_520
                                                                                                                                                                                (coe
                                                                                                                                                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'pair_446
                                                                                                                                                                                   v24
                                                                                                                                                                                   v40))
                                                                                                                                                                             (coe
                                                                                                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                erased
                                                                                                                                                                                (coe
                                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                   erased
                                                                                                                                                                                   (coe
                                                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                      erased
                                                                                                                                                                                      erased)))))))))
                                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'curry_458 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v14 v15 v16
                      -> let v17
                               = d_morph'45'elab_4492
                                   (coe v0) (coe v13)
                                   (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v2) (coe v14))
                                   (coe v16) (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v11) in
                         coe
                           (case coe v17 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                -> case coe v19 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                       -> case coe v21 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                              -> case coe v23 of
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                     -> case coe v25 of
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                            -> case coe v27 of
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                                                   -> case coe v29 of
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                                                          -> case coe v31 of
                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                                                                 -> coe
                                                                                      seq (coe v33)
                                                                                      (coe
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.IR.C_curry_88
                                                                                            v18
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.IR.C_Heap_8))
                                                                                         (coe
                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'curry_458
                                                                                               v20)
                                                                                            (coe
                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.IR.C_curry_88
                                                                                                     v18
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Once.IR.C_Heap_8)))
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                  (coe
                                                                                                     addInt
                                                                                                     (coe
                                                                                                        (1 ::
                                                                                                           Integer))
                                                                                                     (coe
                                                                                                        v24))
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                     (coe
                                                                                                        v26)
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_520
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'curry_458
                                                                                                              v20))
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                           erased
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                              erased
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                 erased
                                                                                                                 erased)))))))))
                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'cata_472 v11 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_132 v16
                      -> coe
                           seq (coe v4)
                           (let v17
                                  = d_morph'45'elab_4492
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_208
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                            (coe v0))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_polys_196
                                            (coe v0)))
                                      (coe v15)
                                      (coe
                                         MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v16)
                                         (coe v3))
                                      (coe v3) (coe v4) (coe v13) in
                            coe
                              (case coe v17 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                   -> case coe v19 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                          -> case coe v21 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                 -> case coe v23 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                        -> case coe v25 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                               -> case coe v27 of
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                                                      -> case coe v29 of
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                                                             -> case coe v31 of
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                                                                    -> coe
                                                                                         seq
                                                                                         (coe v33)
                                                                                         (coe
                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.IR.C_Cata_118
                                                                                               v11
                                                                                               v18)
                                                                                            (coe
                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'cata_472
                                                                                                  v11
                                                                                                  v20)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.Surface.Syntax.C_cata_558
                                                                                                     v11
                                                                                                     v22)
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                     (coe
                                                                                                        addInt
                                                                                                        (coe
                                                                                                           (1 ::
                                                                                                              Integer))
                                                                                                        (coe
                                                                                                           v24))
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                                                                           (coe
                                                                                                              v0))
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_520
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'cata_472
                                                                                                                 v11
                                                                                                                 v20))
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                              erased
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                 erased
                                                                                                                 (coe
                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                    erased
                                                                                                                    erased)))))))))
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_484 v11
        -> coe
             du_const'45'morph'45'strong_4838 (coe v0) (coe v1) (coe v3)
             (coe v11)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named_496
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v14
               -> coe
                    d_named'45'morph'45'strong_4128 v0 v14 v2 v3 v4 erased erased
                    erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named'45'resolved_508
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v12
               -> coe
                    d_named'45'morph'45'strong'45'resolved_4140 v0 v12 v2 v3 v4 erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.morph-complete
d_morph'45'complete_4510 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_morph'45'complete_4510 v0 v1 v2 v3 v4 v5
  = let v6
          = d_morph'45'elab_4492
              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
           -> case coe v8 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                  -> case coe v10 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                         -> case coe v12 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                -> case coe v14 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                       -> case coe v16 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                              -> case coe v18 of
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                     -> case coe v20 of
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                            -> coe
                                                                 seq (coe v22)
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe v11)
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                       (coe v13)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          (coe v15) erased)))
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.pair-eff-complete
d_pair'45'eff'45'complete_4530 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pair'45'eff'45'complete_4530 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = d_morph'45'elab_4492
              (coe v0) (coe v1) (coe v3) (coe v4)
              (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v6) in
    coe
      (let v9
             = d_morph'45'elab_4492
                 (coe v0) (coe v2) (coe v3) (coe v5)
                 (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v7) in
       coe
         (case coe v8 of
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
              -> case coe v11 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                     -> case coe v13 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                            -> case coe v15 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                   -> case coe v17 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                          -> case coe v19 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                 -> case coe v21 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                        -> case coe v23 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                               -> coe
                                                                    seq (coe v25)
                                                                    (case coe v9 of
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                         -> case coe v27 of
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                                                                -> case coe v29 of
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                                                                       -> case coe
                                                                                                 v31 of
                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                                                                              -> case coe
                                                                                                        v33 of
                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                                                                                                     -> case coe
                                                                                                               v35 of
                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
                                                                                                            -> case coe
                                                                                                                      v37 of
                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v38 v39
                                                                                                                   -> case coe
                                                                                                                             v39 of
                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v40 v41
                                                                                                                          -> coe
                                                                                                                               seq
                                                                                                                               (coe
                                                                                                                                  v41)
                                                                                                                               (coe
                                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                  (coe
                                                                                                                                     MAlonzo.Code.Once.Surface.Syntax.C_arr''_496
                                                                                                                                     (coe
                                                                                                                                        MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                                                                                        (coe
                                                                                                                                           MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                                                                                                                                           v10
                                                                                                                                           v26
                                                                                                                                           (coe
                                                                                                                                              MAlonzo.Code.Once.IR.C_Heap_8))))
                                                                                                                                  (coe
                                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                     (coe
                                                                                                                                        addInt
                                                                                                                                        (coe
                                                                                                                                           (1 ::
                                                                                                                                              Integer))
                                                                                                                                        (coe
                                                                                                                                           MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                                                           (coe
                                                                                                                                              v16)
                                                                                                                                           (coe
                                                                                                                                              v32)))
                                                                                                                                     (coe
                                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                        (coe
                                                                                                                                           v34)
                                                                                                                                        erased)))
                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       _ -> MAlonzo.RTE.mazUnreachableError)
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.TypeCheck.Completeness.curry-eff-complete
d_curry'45'eff'45'complete_4548 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_curry'45'eff'45'complete_4548 v0 v1 v2 v3 v4 v5
  = let v6
          = d_morph'45'elab_4492
              (coe v0) (coe v1)
              (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v2) (coe v3))
              (coe v4) (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v5) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
           -> case coe v8 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                  -> case coe v10 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                         -> case coe v12 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                -> case coe v14 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                       -> case coe v16 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                              -> case coe v18 of
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                     -> case coe v20 of
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                            -> coe
                                                                 seq (coe v22)
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe
                                                                       MAlonzo.Code.Once.Surface.Syntax.C_arr''_496
                                                                       (coe
                                                                          MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                          (coe
                                                                             MAlonzo.Code.Once.IR.C_curry_88
                                                                             v7
                                                                             (coe
                                                                                MAlonzo.Code.Once.IR.C_Heap_8))))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                       (coe
                                                                          addInt
                                                                          (coe (1 :: Integer))
                                                                          (coe v13))
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          (coe v15) erased)))
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.compose-eff-hlp
d_compose'45'eff'45'hlp_4580 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compose'45'eff'45'hlp_4580 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 ~v9
                             ~v10 ~v11 v12 ~v13
  = du_compose'45'eff'45'hlp_4580 v6 v7 v8 v12
du_compose'45'eff'45'hlp_4580 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compose'45'eff'45'hlp_4580 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_328 v6 v7 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_330 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Once.Surface.Syntax.C_arr''_496 v0)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) erased))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.compose-eff-complete
d_compose'45'eff'45'complete_4600 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compose'45'eff'45'complete_4600 v0 v1 v2 v3 v4 v5 ~v6 v7 v8
  = du_compose'45'eff'45'complete_4600 v0 v1 v2 v3 v4 v5 v7 v8
du_compose'45'eff'45'complete_4600 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compose'45'eff'45'complete_4600 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = d_morph'45'elab_4492
              (coe v0) (coe v1) (coe v4) (coe v5)
              (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v6) in
    coe
      (let v9
             = d_morph'45'elab_4492
                 (coe v0) (coe v2) (coe v3) (coe v4)
                 (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v7) in
       coe
         (case coe v8 of
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
              -> case coe v11 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                     -> case coe v13 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                            -> case coe v15 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                   -> case coe v17 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                          -> case coe v19 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                 -> case coe v21 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                        -> case coe v23 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                               -> coe
                                                                    seq (coe v25)
                                                                    (case coe v9 of
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                         -> case coe v27 of
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                                                                -> case coe v29 of
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                                                                       -> case coe
                                                                                                 v31 of
                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                                                                              -> case coe
                                                                                                        v33 of
                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                                                                                                     -> case coe
                                                                                                               v35 of
                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
                                                                                                            -> case coe
                                                                                                                      v37 of
                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v38 v39
                                                                                                                   -> case coe
                                                                                                                             v39 of
                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v40 v41
                                                                                                                          -> coe
                                                                                                                               seq
                                                                                                                               (coe
                                                                                                                                  v41)
                                                                                                                               (coe
                                                                                                                                  du_compose'45'eff'45'hlp_4580
                                                                                                                                  (coe
                                                                                                                                     MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                                                                                     (coe
                                                                                                                                        MAlonzo.Code.Once.IR.C__'8728'__30
                                                                                                                                        v4
                                                                                                                                        v10
                                                                                                                                        v26))
                                                                                                                                  (coe
                                                                                                                                     addInt
                                                                                                                                     (coe
                                                                                                                                        (1 ::
                                                                                                                                           Integer))
                                                                                                                                     (coe
                                                                                                                                        MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                                                        (coe
                                                                                                                                           v16)
                                                                                                                                        (coe
                                                                                                                                           v32)))
                                                                                                                                  (coe
                                                                                                                                     v18)
                                                                                                                                  (coe
                                                                                                                                     MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkComposeGo_1588
                                                                                                                                     (coe
                                                                                                                                        v0)
                                                                                                                                     (coe
                                                                                                                                        v1)
                                                                                                                                     (coe
                                                                                                                                        v2)
                                                                                                                                     (coe
                                                                                                                                        v3)
                                                                                                                                     (coe
                                                                                                                                        v5)
                                                                                                                                     (coe
                                                                                                                                        MAlonzo.Code.Once.Type.C_eff_36)
                                                                                                                                     (coe
                                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                        (coe
                                                                                                                                           v4))))
                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       _ -> MAlonzo.RTE.mazUnreachableError)
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.TypeCheck.Completeness.case-eff-complete
d_case'45'eff'45'complete_4620 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_case'45'eff'45'complete_4620 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = d_morph'45'elab_4492
              (coe v0) (coe v1) (coe v3) (coe v5)
              (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v6) in
    coe
      (let v9
             = d_morph'45'elab_4492
                 (coe v0) (coe v2) (coe v4) (coe v5)
                 (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v7) in
       coe
         (case coe v8 of
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
              -> case coe v11 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                     -> case coe v13 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                            -> case coe v15 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                   -> case coe v17 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                          -> case coe v19 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                 -> case coe v21 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                        -> case coe v23 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                               -> coe
                                                                    seq (coe v25)
                                                                    (case coe v9 of
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                         -> case coe v27 of
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                                                                -> case coe v29 of
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                                                                       -> case coe
                                                                                                 v31 of
                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                                                                              -> case coe
                                                                                                        v33 of
                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                                                                                                     -> case coe
                                                                                                               v35 of
                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
                                                                                                            -> case coe
                                                                                                                      v37 of
                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v38 v39
                                                                                                                   -> case coe
                                                                                                                             v39 of
                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v40 v41
                                                                                                                          -> case coe
                                                                                                                                    v41 of
                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v42 v43
                                                                                                                                 -> let v44
                                                                                                                                          = coe
                                                                                                                                              MAlonzo.Code.Once.Type.C_eff_36 in
                                                                                                                                    coe
                                                                                                                                      (let v45
                                                                                                                                             = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_1666
                                                                                                                                                 (coe
                                                                                                                                                    v0)
                                                                                                                                                 (coe
                                                                                                                                                    v1)
                                                                                                                                                 (coe
                                                                                                                                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                                                                                                                                    (coe
                                                                                                                                                       v3)
                                                                                                                                                    (coe
                                                                                                                                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                                                                                       (coe
                                                                                                                                                          MAlonzo.Code.Once.Type.C_Many_10)
                                                                                                                                                       (coe
                                                                                                                                                          MAlonzo.Code.Once.Type.C_eff_36))
                                                                                                                                                    (coe
                                                                                                                                                       v5)) in
                                                                                                                                       coe
                                                                                                                                         (case coe
                                                                                                                                                 v45 of
                                                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v46 v47
                                                                                                                                              -> case coe
                                                                                                                                                        v46 of
                                                                                                                                                   MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_328 v48 v49 v50 v51
                                                                                                                                                     -> let v52
                                                                                                                                                              = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_1666
                                                                                                                                                                  (coe
                                                                                                                                                                     v0)
                                                                                                                                                                  (coe
                                                                                                                                                                     v2)
                                                                                                                                                                  (coe
                                                                                                                                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                                                                                                                                                     (coe
                                                                                                                                                                        v4)
                                                                                                                                                                     (coe
                                                                                                                                                                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                                                                                                        (coe
                                                                                                                                                                           MAlonzo.Code.Once.Type.C_Many_10)
                                                                                                                                                                        (coe
                                                                                                                                                                           v44))
                                                                                                                                                                     (coe
                                                                                                                                                                        v5)) in
                                                                                                                                                        coe
                                                                                                                                                          (case coe
                                                                                                                                                                  v52 of
                                                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v53 v54
                                                                                                                                                               -> case coe
                                                                                                                                                                         v53 of
                                                                                                                                                                    MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_328 v55 v56 v57 v58
                                                                                                                                                                      -> let v59
                                                                                                                                                                               = coe
                                                                                                                                                                                   MAlonzo.Code.Once.TypeCheck.Elaborate.du_extract'45'morph'45'eff'45'aux_784
                                                                                                                                                                                   (coe
                                                                                                                                                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                                                                                                                                                                      (coe
                                                                                                                                                                                         v3)
                                                                                                                                                                                      (coe
                                                                                                                                                                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                                                                                                                         (coe
                                                                                                                                                                                            MAlonzo.Code.Once.Type.C_Many_10)
                                                                                                                                                                                         (coe
                                                                                                                                                                                            v44))
                                                                                                                                                                                      (coe
                                                                                                                                                                                         v5))
                                                                                                                                                                                   (coe
                                                                                                                                                                                      v3)
                                                                                                                                                                                   (coe
                                                                                                                                                                                      v5)
                                                                                                                                                                                   (coe
                                                                                                                                                                                      v44)
                                                                                                                                                                                   (coe
                                                                                                                                                                                      v49) in
                                                                                                                                                                         coe
                                                                                                                                                                           (let v60
                                                                                                                                                                                  = coe
                                                                                                                                                                                      MAlonzo.Code.Once.TypeCheck.Elaborate.du_extract'45'morph'45'eff'45'aux_784
                                                                                                                                                                                      (coe
                                                                                                                                                                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                                                                                                                                                                         (coe
                                                                                                                                                                                            v4)
                                                                                                                                                                                         (coe
                                                                                                                                                                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                                                                                                                            (coe
                                                                                                                                                                                               MAlonzo.Code.Once.Type.C_Many_10)
                                                                                                                                                                                            (coe
                                                                                                                                                                                               v44))
                                                                                                                                                                                         (coe
                                                                                                                                                                                            v5))
                                                                                                                                                                                      (coe
                                                                                                                                                                                         v4)
                                                                                                                                                                                      (coe
                                                                                                                                                                                         v5)
                                                                                                                                                                                      (coe
                                                                                                                                                                                         v44)
                                                                                                                                                                                      (coe
                                                                                                                                                                                         v56) in
                                                                                                                                                                            coe
                                                                                                                                                                              (let v61
                                                                                                                                                                                     = coe
                                                                                                                                                                                         MAlonzo.Code.Once.TypeCheck.Judgment.du_extractMorphWitness_714
                                                                                                                                                                                         (coe
                                                                                                                                                                                            v1)
                                                                                                                                                                                         (coe
                                                                                                                                                                                            v47) in
                                                                                                                                                                               coe
                                                                                                                                                                                 (let v62
                                                                                                                                                                                        = coe
                                                                                                                                                                                            MAlonzo.Code.Once.TypeCheck.Judgment.du_extractMorphWitness_714
                                                                                                                                                                                            (coe
                                                                                                                                                                                               v2)
                                                                                                                                                                                            (coe
                                                                                                                                                                                               v54) in
                                                                                                                                                                                  coe
                                                                                                                                                                                    (case coe
                                                                                                                                                                                            v59 of
                                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v63
                                                                                                                                                                                         -> case coe
                                                                                                                                                                                                   v63 of
                                                                                                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v64 v65
                                                                                                                                                                                                -> case coe
                                                                                                                                                                                                          v60 of
                                                                                                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v66
                                                                                                                                                                                                       -> case coe
                                                                                                                                                                                                                 v66 of
                                                                                                                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v67 v68
                                                                                                                                                                                                              -> case coe
                                                                                                                                                                                                                        v61 of
                                                                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v69
                                                                                                                                                                                                                     -> case coe
                                                                                                                                                                                                                               v62 of
                                                                                                                                                                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v70
                                                                                                                                                                                                                            -> let v71
                                                                                                                                                                                                                                     = coe
                                                                                                                                                                                                                                         MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                                            MAlonzo.Code.Once.IR.C_case_70
                                                                                                                                                                                                                                            v64
                                                                                                                                                                                                                                            v67) in
                                                                                                                                                                                                                               coe
                                                                                                                                                                                                                                 (let v72
                                                                                                                                                                                                                                        = addInt
                                                                                                                                                                                                                                            (coe
                                                                                                                                                                                                                                               (1 ::
                                                                                                                                                                                                                                                  Integer))
                                                                                                                                                                                                                                            (coe
                                                                                                                                                                                                                                               MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                                                  v50)
                                                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                                                  v57)) in
                                                                                                                                                                                                                                  coe
                                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                                                                       (coe
                                                                                                                                                                                                                                          v71)
                                                                                                                                                                                                                                       (coe
                                                                                                                                                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                                             v72)
                                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                                                v51)
                                                                                                                                                                                                                                             erased))))
                                                                                                                                                                                                                          _ -> coe
                                                                                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                                    MAlonzo.Code.Once.Surface.Syntax.C_arr''_496
                                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                                       MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                                                                                                                                                                                       (coe
                                                                                                                                                                                                                                          MAlonzo.Code.Once.IR.C_case_70
                                                                                                                                                                                                                                          v10
                                                                                                                                                                                                                                          v26)))
                                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                                       addInt
                                                                                                                                                                                                                                       (coe
                                                                                                                                                                                                                                          (1 ::
                                                                                                                                                                                                                                             Integer))
                                                                                                                                                                                                                                       (coe
                                                                                                                                                                                                                                          MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                                             v16)
                                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                                             v32)))
                                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                                                                       (coe
                                                                                                                                                                                                                                          v18)
                                                                                                                                                                                                                                       erased))
                                                                                                                                                                                                                   _ -> coe
                                                                                                                                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                             MAlonzo.Code.Once.Surface.Syntax.C_arr''_496
                                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                                MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                                                                                                                                                                                (coe
                                                                                                                                                                                                                                   MAlonzo.Code.Once.IR.C_case_70
                                                                                                                                                                                                                                   v10
                                                                                                                                                                                                                                   v26)))
                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                                addInt
                                                                                                                                                                                                                                (coe
                                                                                                                                                                                                                                   (1 ::
                                                                                                                                                                                                                                      Integer))
                                                                                                                                                                                                                                (coe
                                                                                                                                                                                                                                   MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                                      v16)
                                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                                      v32)))
                                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                                                                (coe
                                                                                                                                                                                                                                   v18)
                                                                                                                                                                                                                                erased))
                                                                                                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                                     _ -> coe
                                                                                                                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                                            (coe
                                                                                                                                                                                                               MAlonzo.Code.Once.Surface.Syntax.C_arr''_496
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     MAlonzo.Code.Once.IR.C_case_70
                                                                                                                                                                                                                     v10
                                                                                                                                                                                                                     v26)))
                                                                                                                                                                                                            (coe
                                                                                                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  addInt
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     (1 ::
                                                                                                                                                                                                                        Integer))
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                        v16)
                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                        v32)))
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     v18)
                                                                                                                                                                                                                  erased))
                                                                                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                                                       _ -> coe
                                                                                                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                              (coe
                                                                                                                                                                                                 MAlonzo.Code.Once.Surface.Syntax.C_arr''_496
                                                                                                                                                                                                 (coe
                                                                                                                                                                                                    MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                                                                                                                                                    (coe
                                                                                                                                                                                                       MAlonzo.Code.Once.IR.C_case_70
                                                                                                                                                                                                       v10
                                                                                                                                                                                                       v26)))
                                                                                                                                                                                              (coe
                                                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                                 (coe
                                                                                                                                                                                                    addInt
                                                                                                                                                                                                    (coe
                                                                                                                                                                                                       (1 ::
                                                                                                                                                                                                          Integer))
                                                                                                                                                                                                    (coe
                                                                                                                                                                                                       MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                                                                                                                       (coe
                                                                                                                                                                                                          v16)
                                                                                                                                                                                                       (coe
                                                                                                                                                                                                          v32)))
                                                                                                                                                                                                 (coe
                                                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                                    (coe
                                                                                                                                                                                                       v18)
                                                                                                                                                                                                    erased))))))
                                                                                                                                                                    MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_330 v55
                                                                                                                                                                      -> coe
                                                                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                           (coe
                                                                                                                                                                              MAlonzo.Code.Once.Surface.Syntax.C_arr''_496
                                                                                                                                                                              (coe
                                                                                                                                                                                 MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                                                                                                                                 (coe
                                                                                                                                                                                    MAlonzo.Code.Once.IR.C_case_70
                                                                                                                                                                                    v10
                                                                                                                                                                                    v26)))
                                                                                                                                                                           (coe
                                                                                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                              (coe
                                                                                                                                                                                 addInt
                                                                                                                                                                                 (coe
                                                                                                                                                                                    (1 ::
                                                                                                                                                                                       Integer))
                                                                                                                                                                                 (coe
                                                                                                                                                                                    MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                                                                                                    (coe
                                                                                                                                                                                       v16)
                                                                                                                                                                                    (coe
                                                                                                                                                                                       v32)))
                                                                                                                                                                              (coe
                                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                                 (coe
                                                                                                                                                                                    v18)
                                                                                                                                                                                 erased))
                                                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                                                                                   MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_330 v48
                                                                                                                                                     -> coe
                                                                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                          (coe
                                                                                                                                                             MAlonzo.Code.Once.Surface.Syntax.C_arr''_496
                                                                                                                                                             (coe
                                                                                                                                                                MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                                                                                                                (coe
                                                                                                                                                                   MAlonzo.Code.Once.IR.C_case_70
                                                                                                                                                                   v10
                                                                                                                                                                   v26)))
                                                                                                                                                          (coe
                                                                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                             (coe
                                                                                                                                                                addInt
                                                                                                                                                                (coe
                                                                                                                                                                   (1 ::
                                                                                                                                                                      Integer))
                                                                                                                                                                (coe
                                                                                                                                                                   MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                                                                                   (coe
                                                                                                                                                                      v16)
                                                                                                                                                                   (coe
                                                                                                                                                                      v32)))
                                                                                                                                                             (coe
                                                                                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                (coe
                                                                                                                                                                   v18)
                                                                                                                                                                erased))
                                                                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       _ -> MAlonzo.RTE.mazUnreachableError)
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.TypeCheck.Completeness.cata-eff-complete
d_cata'45'eff'45'complete_4638 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'eff'45'complete_4638 v0 v1 v2 v3 v4 ~v5 v6
  = du_cata'45'eff'45'complete_4638 v0 v1 v2 v3 v4 v6
du_cata'45'eff'45'complete_4638 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cata'45'eff'45'complete_4638 v0 v1 v2 v3 v4 v5
  = let v6
          = d_morph'45'elab_4492
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_208
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194 (coe v0))
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_196 (coe v0)))
              (coe v1)
              (coe
                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v2) (coe v3))
              (coe v3) (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v5) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
           -> case coe v8 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                  -> case coe v10 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                         -> case coe v12 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                -> case coe v14 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                       -> case coe v16 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                              -> case coe v18 of
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                     -> case coe v20 of
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                            -> coe
                                                                 seq (coe v22)
                                                                 (let v23
                                                                        = coe
                                                                            MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkCataGo_1644
                                                                            (coe v0) (coe v1)
                                                                            (coe v2) (coe v3)
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C_eff_36)
                                                                            (coe
                                                                               MAlonzo.Code.Once.Functor.Decide.d_wellFormedF'63'_52
                                                                               (coe v2)) in
                                                                  coe
                                                                    (case coe v23 of
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                                         -> case coe v24 of
                                                                              MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_328 v26 v27 v28 v29
                                                                                -> coe
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                     (coe v27)
                                                                                     (coe
                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                        (coe v28)
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                           (coe v29)
                                                                                           erased))
                                                                              MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_330 v26
                                                                                -> coe
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Surface.Syntax.C_arr''_496
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Surface.Syntax.C_cata_558
                                                                                           v4 v11))
                                                                                     (coe
                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                        (coe
                                                                                           addInt
                                                                                           (coe
                                                                                              (1 ::
                                                                                                 Integer))
                                                                                           (coe
                                                                                              v13))
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                                                              (coe
                                                                                                 v0))
                                                                                           erased))
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.check-completeV
d_check'45'completeV_4656 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_check'45'completeV_4656 v0 v1 v2 ~v3 v4
  = du_check'45'completeV_4656 v0 v1 v2 v4
du_check'45'completeV_4656 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_check'45'completeV_4656 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_1666
              (coe v0) (coe v1) (coe v2) in
    coe
      (let v5
             = coe
                 du_check'45'complete_4854 (coe v0) (coe v1) (coe v2) (coe v3) in
       coe
         (case coe v4 of
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
              -> case coe v5 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                     -> case coe v9 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                            -> case coe v11 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v7) erased)))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.TypeCheck.Completeness.iFromInfer
d_iFromInfer_4672 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_iFromInfer_4672 v0 v1 v2 ~v3 v4 = du_iFromInfer_4672 v0 v1 v2 v4
du_iFromInfer_4672 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_iFromInfer_4672 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_30
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v6
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab'45'fallback'45'RInt_9552
                    (coe v0) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'str_36
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_56 v6
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab'45'fallback'45'RStringLit_9582
                    (coe v0) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_40
        -> coe
             MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab'45'fallback'45'RUnit_9610
             (coe v0)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_44
        -> coe
             MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab'45'fallback'45'RVar'45'unit_10624
             (coe v0)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_56 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v11
               -> coe
                    du_checkElab'45'fallback'45'RVar_2010 (coe v0) (coe v11) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_66
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v9 v10
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RQualified_9646
                    (coe v0) (coe v9) (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_74
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v8
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RResolved_9804
                    (coe v0) (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_82
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v10
               -> coe
                    du_checkElab'45'fallback'45'RVar_2010 (coe v0) (coe v10) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_92 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_58 v9 v10
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RAnnot_9948
                    (coe v0) (coe v9) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_108 v9 v10 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v13 v14
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__126 v15 v16
                      -> let v17
                               = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      du_iFromInfer_4672 (coe v0) (coe v13) (coe v15) (coe v11)) in
                         coe
                           (let v18
                                  = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            du_iFromInfer_4672 (coe v0) (coe v13) (coe v15)
                                            (coe v11))) in
                            coe
                              (coe
                                 du_pair'45'lit'45'reduce_4728 (coe v9) (coe v10) (coe v17)
                                 (coe v18)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe du_iFromInfer_4672 (coe v0) (coe v14) (coe v16) (coe v12)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          du_iFromInfer_4672 (coe v0) (coe v14) (coe v16)
                                          (coe v12))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             du_iFromInfer_4672 (coe v0) (coe v14) (coe v16)
                                             (coe v12)))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_116 v7
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_62 v9
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RUnaryOp_10478
                    (coe v0) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_136 v8 v10 v11 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v15 v16 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RLet_10096
                    (coe v0) (coe v15) (coe v16) (coe v17)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_166 v10 v11 v13 v14 v15 v16 v17 v18 v19 v20
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v21 v22 v23 v24 v25
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RDestruct_10276
                    (coe v0) (coe v21) (coe v22) (coe v23) (coe v24) (coe v25)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_180 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_60 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RBinOp_14484
                    (coe v0) (coe v13) (coe v14) (coe v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_194 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_60 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RBinOp_14484
                    (coe v0) (coe v13) (coe v14) (coe v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_204 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RApp'45'id_13122
                    (coe v0) (coe v10) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_216 v7 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RApp'45'fst_13192
                    (coe v0) (coe v11) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_228 v6 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RApp'45'snd_13262
                    (coe v0) (coe v11) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_238 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RApp'45'terminal_14410
                    (coe v0) (coe v10) (coe MAlonzo.Code.Once.Type.C_Unit_122)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_250 v6 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RApp'45'apply_11564
                    (coe v0) (coe v11) (coe v6) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_268 v7 v9 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RApp'45'generic_13348
                    (coe v0) (coe v15) (coe v16) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_284 v7 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v16 v17 v18
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RApp'45'generic_13348
                           (coe v0) (coe v14) (coe v15)
                           (coe
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                              (coe MAlonzo.Code.Once.Type.C_Unit_122)
                              (coe
                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                 (coe MAlonzo.Code.Once.Type.C_eff_36))
                              (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.check-completeV-from-infer
d_check'45'completeV'45'from'45'infer_4690 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_check'45'completeV'45'from'45'infer_4690 v0 v1 v2 ~v3 v4
  = du_check'45'completeV'45'from'45'infer_4690 v0 v1 v2 v4
du_check'45'completeV'45'from'45'infer_4690 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_check'45'completeV'45'from'45'infer_4690 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_1666
              (coe v0) (coe v1) (coe v2) in
    coe
      (let v5
             = coe du_iFromInfer_4672 (coe v0) (coe v1) (coe v2) (coe v3) in
       coe
         (case coe v4 of
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
              -> case coe v5 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                     -> case coe v9 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                            -> case coe v11 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v7) erased)))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.TypeCheck.Completeness.pair-lit-reduce
d_pair'45'lit'45'reduce_4728 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pair'45'lit'45'reduce_4728 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 ~v9
                             ~v10 v11 v12 v13 ~v14 ~v15 ~v16
  = du_pair'45'lit'45'reduce_4728 v5 v6 v7 v8 v11 v12 v13
du_pair'45'lit'45'reduce_4728 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pair'45'lit'45'reduce_4728 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_pair_252 v0 v1 v2 v4)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v3) (coe v5))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) erased))
-- Once.TypeCheck.Completeness.iFromInferEff
d_iFromInferEff_4746 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_iFromInferEff_4746 v0 v1 v2 v3 ~v4 v5
  = du_iFromInferEff_4746 v0 v1 v2 v3 v5
du_iFromInferEff_4746 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_iFromInferEff_4746 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_56 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RVar'45'eff_13908
                    (coe v0) (coe v12) (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_66
        -> coe
             du_embedOrSubsume'45'lifts_2522 (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658 (coe v0)
                (coe v1))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_74
        -> coe
             du_embedOrSubsume'45'lifts_2522 (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658 (coe v0)
                (coe v1))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_82
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RVar'45'eff_13908
                    (coe v0) (coe v11) (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_92 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_58 v10 v11
               -> coe
                    du_embedOrSubsume'45'lifts_2522 (coe v2) (coe v3)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658 (coe v0)
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_58 (coe v10)
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v2)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe v3))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_136 v9 v11 v12 v13 v14 v15
        -> coe
             du_embedOrSubsume'45'lifts_2522 (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658 (coe v0)
                (coe v1))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_166 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21
        -> coe
             du_embedOrSubsume'45'lifts_2522 (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658 (coe v0)
                (coe v1))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_204 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RApp'45'id'45'eff_13578
                    (coe v0) (coe v11) (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_216 v8 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RApp'45'fst'45'eff_13688
                    (coe v0) (coe v12) (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_228 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RApp'45'snd'45'eff_13798
                    (coe v0) (coe v12) (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_250 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RApp'45'apply'45'eff_14060
                    (coe v0) (coe v12) (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_268 v8 v10 v11 v12 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RApp'45'generic'45'eff_13436
                    (coe v0) (coe v16) (coe v17) (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.infer-complete
d_infer'45'complete_4762 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete_4762 v0 v1 v2 ~v3 v4
  = du_infer'45'complete_4762 v0 v1 v2 v4
du_infer'45'complete_4762 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete_4762 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_30
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v6
               -> coe d_infer'45'complete'45'RInt_16 (coe v0) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'str_36
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_56 v6
               -> coe d_infer'45'complete'45'RStringLit_30 (coe v0) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_40
        -> coe d_infer'45'complete'45'RUnit_42 (coe v0)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_44
        -> coe d_infer'45'complete'45'RVar'45'unit_52 (coe v0)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_56 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v11
               -> coe
                    du_infer'45'complete'45'RVar'45'local_740 (coe v0) (coe v11)
                    (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_66
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v9 v10
               -> coe
                    du_infer'45'complete'45'RQualified_68 (coe v0) (coe v9) (coe v10)
                    (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_74
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v8
               -> coe
                    du_infer'45'complete'45'RResolved_170 (coe v0) (coe v8) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_82
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v10
               -> coe
                    du_infer'45'complete'45'RVar'45'import_814 (coe v0) (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_92 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_58 v9 v10
               -> coe
                    du_infer'45'complete'45'RAnnot_386 (coe v0) (coe v9) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_108 v9 v10 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v13 v14
               -> coe
                    du_infer'45'complete'45'RPair_290 (coe v0) (coe v13) (coe v14)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_116 v7
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_62 v9
               -> coe
                    du_infer'45'complete'45'RUnaryOp'45'neg_348 (coe v0) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_136 v8 v10 v11 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v15 v16 v17
               -> coe
                    du_infer'45'complete'45'RLet_444 (coe v0) (coe v15) (coe v16)
                    (coe v17)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_166 v10 v11 v13 v14 v15 v16 v17 v18 v19 v20
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v21 v22 v23 v24 v25
               -> coe
                    du_infer'45'complete'45'RDestruct_1598 (coe v0) (coe v21) (coe v22)
                    (coe v23) (coe v24) (coe v25) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_180 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_60 v13 v14 v15
               -> coe
                    du_infer'45'complete'45'RBinOp'45'arith_908 (coe v0) (coe v13)
                    (coe v14) (coe v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_194 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_60 v13 v14 v15
               -> coe
                    du_infer'45'complete'45'RBinOp'45'cmp_1132 (coe v0) (coe v13)
                    (coe v14) (coe v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_204 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> coe du_infer'45'complete'45'RApp'45'id_516 (coe v0) (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_216 v7 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe du_infer'45'complete'45'RApp'45'fst_594 (coe v0) (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_228 v6 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe du_infer'45'complete'45'RApp'45'snd_634 (coe v0) (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_238 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> coe
                    du_infer'45'complete'45'RApp'45'terminal_554 (coe v0) (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_250 v6 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    du_infer'45'complete'45'RApp'45'apply_674 (coe v0) (coe v11)
                    (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_268 v7 v9 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> coe
                    du_infer'45'complete'45'RApp'45'generic_1796 (coe v0) (coe v15)
                    (coe v16) (coe v7) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_284 v7 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> coe
                    du_infer'45'complete'45'RApp'45'eff_1924 (coe v0) (coe v14)
                    (coe v15) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.nothing≢just
d_nothing'8802'just_4772 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  () -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_nothing'8802'just_4772 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_nothing'8802'just_4772
du_nothing'8802'just_4772 :: AgdaAny
du_nothing'8802'just_4772 = MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.checkG-just
d_checkG'45'just_4788 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkG'45'just_4788 v0 v1 v2 ~v3 v4
  = du_checkG'45'just_4788 v0 v1 v2 v4
du_checkG'45'just_4788 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkG'45'just_4788 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'int_290
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Once.Surface.Elaborate.du_intLit_8 (coe v6))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'int_290) erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'terminal_294
        -> let v7
                 = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                     (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                     (coe ("terminal" :: Data.Text.Text))
                     (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190 (coe v0)) in
           coe
             (case coe v7 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                  -> case coe v8 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                         -> coe seq (coe v10) (coe du_nothing'8802'just_4772)
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> let v8
                           = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                               (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194 (coe v0))
                               (coe ("terminal" :: Data.Text.Text)) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                            -> coe du_nothing'8802'just_4772
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe MAlonzo.Code.Once.IR.C_terminal_74)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'terminal_294)
                                    erased)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'pair_306 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__126 v13 v14
                      -> let v15
                               = coe
                                   du_checkG'45'just_4788 (coe v0) (coe v11) (coe v13) (coe v9) in
                         coe
                           (let v16
                                  = coe
                                      du_checkG'45'just_4788 (coe v0) (coe v12) (coe v14)
                                      (coe v10) in
                            coe
                              (case coe v15 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                   -> case coe v18 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                          -> case coe v16 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                 -> case coe v22 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                                        -> coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe
                                                                MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                                                                v17 v21
                                                                (coe MAlonzo.Code.Once.IR.C_Heap_8))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'pair_306
                                                                   v19 v23)
                                                                erased)
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inl_316 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v11 v12
                      -> let v13
                               = coe
                                   du_checkG'45'just_4788 (coe v0) (coe v10) (coe v11) (coe v8) in
                         coe
                           (case coe v13 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                -> case coe v15 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               MAlonzo.Code.Once.IR.C__'8728'__30 v11
                                               (coe
                                                  MAlonzo.Code.Once.IR.C_inl_56
                                                  (coe MAlonzo.Code.Once.IR.C_Heap_8))
                                               v14)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inl_316
                                                  v16)
                                               erased)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inr_326 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v11 v12
                      -> let v13
                               = coe
                                   du_checkG'45'just_4788 (coe v0) (coe v10) (coe v12) (coe v8) in
                         coe
                           (case coe v13 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                -> case coe v15 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               MAlonzo.Code.Once.IR.C__'8728'__30 v12
                                               (coe
                                                  MAlonzo.Code.Once.IR.C_inr_62
                                                  (coe MAlonzo.Code.Once.IR.C_Heap_8))
                                               v14)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inr_326
                                                  v16)
                                               erased)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'In_336 v7 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_132 v12
                      -> let v13
                               = coe
                                   du_checkG'45'just_4788 (coe v0) (coe v11)
                                   (coe
                                      MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v12)
                                      (coe v2))
                                   (coe v9) in
                         coe
                           (let v14
                                  = MAlonzo.Code.Once.Functor.Decide.d_wellFormedF'63'_52
                                      (coe v12) in
                            coe
                              (case coe v14 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                   -> case coe v13 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                          -> case coe v17 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                 -> coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         MAlonzo.Code.Once.IR.C__'8728'__30
                                                         (MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166
                                                            (coe v12) (coe v2))
                                                         (coe
                                                            MAlonzo.Code.Once.IR.C_In_108 v15
                                                            (coe MAlonzo.Code.Once.IR.C_Heap_8))
                                                         v16)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'In_336
                                                            v15 v18)
                                                         erased)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                   -> coe du_nothing'8802'just_4772
                                 _ -> MAlonzo.RTE.mazUnreachableError))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.gd-completeV
d_gd'45'completeV_4808 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_gd'45'completeV_4808 v0 v1 v2 ~v3 ~v4 v5
  = du_gd'45'completeV_4808 v0 v1 v2 v5
du_gd'45'completeV_4808 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_gd'45'completeV_4808 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'int_290
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                       (coe MAlonzo.Code.Once.Surface.Elaborate.du_intLit_8 (coe v6)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192 (coe v0))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_560
                                (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'int_290))
                             erased)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'terminal_294
        -> coe
             MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RVar'45'terminalV_11110
             (coe v0)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'pair_306 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__126 v13 v14
                      -> let v15
                               = coe
                                   MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkG_870 (coe v0)
                                   (coe v11) (coe v13) in
                         coe
                           (let v16
                                  = coe
                                      MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkG_870 (coe v0)
                                      (coe v12) (coe v14) in
                            coe
                              (case coe v15 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                   -> case coe v17 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                          -> case coe v16 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v20
                                                 -> case coe v20 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                        -> let v23
                                                                 = coe
                                                                     MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                                                                     v18 v21
                                                                     (coe
                                                                        MAlonzo.Code.Once.IR.C_Heap_8) in
                                                           coe
                                                             (let v24
                                                                    = coe
                                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'pair_306
                                                                        v19 v22 in
                                                              coe
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe
                                                                      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                      v23)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe (0 :: Integer))
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                         (coe
                                                                            MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                                            (coe v0))
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                            (coe
                                                                               MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_560
                                                                               v24)
                                                                            erased)))))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> coe du_nothing'8802'just_4772
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> coe du_nothing'8802'just_4772))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inl_316 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v11 v12
                      -> let v13
                               = coe
                                   MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkG_870 (coe v0)
                                   (coe v10) (coe v11) in
                         coe
                           (case coe v13 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                -> case coe v14 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                       -> let v17
                                                = coe
                                                    MAlonzo.Code.Once.IR.C__'8728'__30 v11
                                                    (coe
                                                       MAlonzo.Code.Once.IR.C_inl_56
                                                       (coe MAlonzo.Code.Once.IR.C_Heap_8))
                                                    v15 in
                                          coe
                                            (let v18
                                                   = coe
                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inl_316
                                                       v16 in
                                             coe
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                     v17)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe (0 :: Integer))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe
                                                           MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                           (coe v0))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe
                                                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_560
                                                              v18)
                                                           erased)))))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                -> case coe v13 of
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                       -> case coe v14 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                              -> coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                      v15)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe (0 :: Integer))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                            (coe v0))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_560
                                                               v16)
                                                            erased)))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                       -> coe du_nothing'8802'just_4772
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inr_326 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v11 v12
                      -> let v13
                               = coe
                                   MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkG_870 (coe v0)
                                   (coe v10) (coe v12) in
                         coe
                           (case coe v13 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                -> case coe v14 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                       -> let v17
                                                = coe
                                                    MAlonzo.Code.Once.IR.C__'8728'__30 v12
                                                    (coe
                                                       MAlonzo.Code.Once.IR.C_inr_62
                                                       (coe MAlonzo.Code.Once.IR.C_Heap_8))
                                                    v15 in
                                          coe
                                            (let v18
                                                   = coe
                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inr_326
                                                       v16 in
                                             coe
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                     v17)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe (0 :: Integer))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe
                                                           MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                           (coe v0))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe
                                                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_560
                                                              v18)
                                                           erased)))))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                -> case coe v13 of
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                       -> case coe v14 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                              -> coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                      v15)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe (0 :: Integer))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                            (coe v0))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_560
                                                               v16)
                                                            erased)))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                       -> coe du_nothing'8802'just_4772
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'In_336 v7 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_132 v12
                      -> let v13
                               = MAlonzo.Code.Once.Functor.Decide.d_wellFormedF'63'_52
                                   (coe v12) in
                         coe
                           (case coe v13 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                -> let v15
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkG_870
                                             (coe v0) (coe v11)
                                             (coe
                                                MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166
                                                (coe v12) (coe v2)) in
                                   coe
                                     (case coe v15 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                          -> case coe v16 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                 -> let v19
                                                          = coe
                                                              MAlonzo.Code.Once.IR.C__'8728'__30
                                                              (MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166
                                                                 (coe v12) (coe v2))
                                                              (coe
                                                                 MAlonzo.Code.Once.IR.C_In_108 v14
                                                                 (coe
                                                                    MAlonzo.Code.Once.IR.C_Heap_8))
                                                              v17 in
                                                    coe
                                                      (let v20
                                                             = coe
                                                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'In_336
                                                                 v14 v18 in
                                                       coe
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe
                                                               MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                               v19)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe (0 :: Integer))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe
                                                                     MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                                     (coe v0))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                     (coe
                                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_560
                                                                        v20)
                                                                     erased)))))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> case coe v15 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                 -> case coe v16 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                        -> coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe
                                                                MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                v17)
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe (0 :: Integer))
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe
                                                                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                                      (coe v0))
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe
                                                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_560
                                                                         v18)
                                                                      erased)))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                 -> let v16
                                                          = coe
                                                              du_checkG'45'just_4788 (coe v0)
                                                              (coe v11)
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166
                                                                 (coe v12) (coe v2))
                                                              (coe v9) in
                                                    coe
                                                      (case coe v16 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                           -> coe
                                                                seq (coe v18)
                                                                (coe du_nothing'8802'just_4772)
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                -> let v14 = coe du_nothing'8802'just_4772 in
                                   coe
                                     (case coe v14 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                          -> coe seq (coe v16) (coe v14)
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.gd-complete
d_gd'45'complete_4826 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_gd'45'complete_4826 v0 v1 v2 ~v3 ~v4 v5
  = du_gd'45'complete_4826 v0 v1 v2 v5
du_gd'45'complete_4826 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_gd'45'complete_4826 v0 v1 v2 v3
  = let v4
          = coe
              du_gd'45'completeV_4808 (coe v0) (coe v1) (coe v2) (coe v3) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v6 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                  -> case coe v8 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                         -> coe
                              seq (coe v10)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                       erased)))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.const-morph-strong
d_const'45'morph'45'strong_4838 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_const'45'morph'45'strong_4838 v0 v1 ~v2 v3 ~v4 v5
  = du_const'45'morph'45'strong_4838 v0 v1 v3 v5
du_const'45'morph'45'strong_4838 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_const'45'morph'45'strong_4838 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'int_290
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Once.Surface.Elaborate.du_intLit_8 (coe v6))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_484
                          (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'int_290))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                             (coe MAlonzo.Code.Once.Surface.Elaborate.du_intLit_8 (coe v6)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192 (coe v0))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                   (coe
                                      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_560
                                      (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'int_290))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                            erased))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'terminal_294
        -> let v7
                 = coe
                     MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1854
                     (coe v0) (coe ("terminal" :: Data.Text.Text))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                        (coe ("terminal" :: Data.Text.Text))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190 (coe v0)))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194 (coe v0))
                        (coe ("terminal" :: Data.Text.Text))) in
           coe
             (case coe v7 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                  -> coe
                       seq (coe v8)
                       (let v10
                              = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                                  (coe ("terminal" :: Data.Text.Text))
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190
                                     (coe v0)) in
                        coe
                          (case coe v10 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                               -> case coe v11 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                      -> coe seq (coe v13) (coe du_nothing'8802'just_4772)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                               -> let v11
                                        = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                               (coe v0))
                                            (coe ("terminal" :: Data.Text.Text)) in
                                  coe
                                    (case coe v11 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                         -> coe du_nothing'8802'just_4772
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                              (coe MAlonzo.Code.Once.IR.C_terminal_74)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe
                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'terminal_372)
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe
                                                       MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                       (coe MAlonzo.Code.Once.IR.C_terminal_74))
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe (0 :: Integer))
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                             (coe v0))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_520
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'terminal_372))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                erased
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   erased
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      erased erased))))))))
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                             _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'pair_306 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__126 v13 v14
                      -> let v15
                               = coe
                                   MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkG_870 (coe v0)
                                   (coe v11) (coe v13) in
                         coe
                           (let v16
                                  = coe
                                      MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkG_870 (coe v0)
                                      (coe v12) (coe v14) in
                            coe
                              (case coe v15 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                   -> case coe v17 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                          -> case coe v16 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v20
                                                 -> case coe v20 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                                        -> let v23
                                                                 = coe
                                                                     MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                                                                     v18 v21
                                                                     (coe
                                                                        MAlonzo.Code.Once.IR.C_Heap_8) in
                                                           coe
                                                             (let v24
                                                                    = coe
                                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'pair_306
                                                                        v19 v22 in
                                                              coe
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe v23)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe
                                                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_484
                                                                         v24)
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                         (coe
                                                                            MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                            v23)
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                            (coe (0 :: Integer))
                                                                            (coe
                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                               (coe
                                                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                                                  (coe v0))
                                                                               (coe
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_560
                                                                                     v24)
                                                                                  (coe
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                     erased
                                                                                     (coe
                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                        erased
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                           erased
                                                                                           erased))))))))))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> coe du_nothing'8802'just_4772
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> coe du_nothing'8802'just_4772))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inl_316 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v11 v12
                      -> let v13
                               = coe
                                   MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkG_870 (coe v0)
                                   (coe v10) (coe v11) in
                         coe
                           (case coe v13 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                -> case coe v14 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                       -> let v17
                                                = coe
                                                    MAlonzo.Code.Once.IR.C__'8728'__30 v11
                                                    (coe
                                                       MAlonzo.Code.Once.IR.C_inl_56
                                                       (coe MAlonzo.Code.Once.IR.C_Heap_8))
                                                    v15 in
                                          coe
                                            (let v18
                                                   = coe
                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inl_316
                                                       v16 in
                                             coe
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v17)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_484
                                                        v18)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe
                                                           MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                           v17)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe (0 :: Integer))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe
                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                                 (coe v0))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe
                                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_560
                                                                    v18)
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    erased
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                       erased
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          erased erased))))))))))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                -> case coe v13 of
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                       -> case coe v14 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                              -> coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe v15)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_484
                                                         v16)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                            v15)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe (0 :: Integer))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                                  (coe v0))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe
                                                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_560
                                                                     v16)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                     erased
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                        erased
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           erased erased))))))))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                       -> coe du_nothing'8802'just_4772
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inr_326 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v11 v12
                      -> let v13
                               = coe
                                   MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkG_870 (coe v0)
                                   (coe v10) (coe v12) in
                         coe
                           (case coe v13 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                -> case coe v14 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                       -> let v17
                                                = coe
                                                    MAlonzo.Code.Once.IR.C__'8728'__30 v12
                                                    (coe
                                                       MAlonzo.Code.Once.IR.C_inr_62
                                                       (coe MAlonzo.Code.Once.IR.C_Heap_8))
                                                    v15 in
                                          coe
                                            (let v18
                                                   = coe
                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inr_326
                                                       v16 in
                                             coe
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v17)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_484
                                                        v18)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe
                                                           MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                           v17)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe (0 :: Integer))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe
                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                                 (coe v0))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe
                                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_560
                                                                    v18)
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    erased
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                       erased
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          erased erased))))))))))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                -> case coe v13 of
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                       -> case coe v14 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                              -> coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe v15)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_484
                                                         v16)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                            v15)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe (0 :: Integer))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                                  (coe v0))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe
                                                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_560
                                                                     v16)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                     erased
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                        erased
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           erased erased))))))))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                       -> coe du_nothing'8802'just_4772
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'In_336 v7 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_132 v12
                      -> let v13
                               = MAlonzo.Code.Once.Functor.Decide.d_wellFormedF'63'_52
                                   (coe v12) in
                         coe
                           (case coe v13 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                -> let v15
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkG_870
                                             (coe v0) (coe v11)
                                             (coe
                                                MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166
                                                (coe v12) (coe v2)) in
                                   coe
                                     (case coe v15 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                          -> case coe v16 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                 -> let v19
                                                          = coe
                                                              MAlonzo.Code.Once.IR.C__'8728'__30
                                                              (MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166
                                                                 (coe v12) (coe v2))
                                                              (coe
                                                                 MAlonzo.Code.Once.IR.C_In_108 v14
                                                                 (coe
                                                                    MAlonzo.Code.Once.IR.C_Heap_8))
                                                              v17 in
                                                    coe
                                                      (let v20
                                                             = coe
                                                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'In_336
                                                                 v14 v18 in
                                                       coe
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe v19)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_484
                                                                  v20)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe
                                                                     MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                     v19)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                     (coe (0 :: Integer))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                        (coe
                                                                           MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                                           (coe v0))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe
                                                                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_560
                                                                              v20)
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                              erased
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                 erased
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    erased
                                                                                    erased))))))))))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> case coe v15 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                 -> case coe v16 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                        -> coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe v17)
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_484
                                                                   v18)
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe
                                                                      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                      v17)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe (0 :: Integer))
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                         (coe
                                                                            MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                                            (coe v0))
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                            (coe
                                                                               MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_560
                                                                               v18)
                                                                            (coe
                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                               erased
                                                                               (coe
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                  erased
                                                                                  (coe
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                     erased
                                                                                     erased))))))))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                 -> let v16
                                                          = coe
                                                              du_checkG'45'just_4788 (coe v0)
                                                              (coe v11)
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166
                                                                 (coe v12) (coe v2))
                                                              (coe v9) in
                                                    coe
                                                      (case coe v16 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                           -> coe
                                                                seq (coe v18)
                                                                (coe du_nothing'8802'just_4772)
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                -> let v14 = coe du_nothing'8802'just_4772 in
                                   coe
                                     (case coe v14 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                          -> coe seq (coe v16) (coe v14)
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.check-complete
d_check'45'complete_4854 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_check'45'complete_4854 v0 v1 v2 ~v3 v4
  = du_check'45'complete_4854 v0 v1 v2 v4
du_check'45'complete_4854 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_check'45'complete_4854 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_520 v9
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v10 v11 v12
               -> case coe v11 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v13 v14
                      -> coe
                           d_morph'45'complete_4510 (coe v0) (coe v1) (coe v10) (coe v12)
                           (coe v14) (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_530 v8
        -> coe du_iFromInfer_4672 (coe v0) (coe v1) (coe v2) (coe v8)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_548 v10 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v16 v17 v18
                      -> case coe v17 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v19 v20
                             -> coe
                                  du_check'45'complete'45'RLam_1398 (coe v0) (coe v14) (coe v15)
                                  (coe v16) (coe v19) (coe v10) (coe v18)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_560 v9
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v10 v11 v12
               -> coe du_gd'45'complete_4826 (coe v0) (coe v1) (coe v12) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_576 v9 v10 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v13 v14
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__126 v15 v16
                      -> let v17
                               = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      du_check'45'complete_4854 (coe v0) (coe v13) (coe v15)
                                      (coe v11)) in
                         coe
                           (let v18
                                  = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            du_check'45'complete_4854 (coe v0) (coe v13) (coe v15)
                                            (coe v11))) in
                            coe
                              (coe
                                 du_pair'45'lit'45'reduce_4728 (coe v9) (coe v10) (coe v17)
                                 (coe v18)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       du_check'45'complete_4854 (coe v0) (coe v14) (coe v16)
                                       (coe v12)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          du_check'45'complete_4854 (coe v0) (coe v14) (coe v16)
                                          (coe v12))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             du_check'45'complete_4854 (coe v0) (coe v14) (coe v16)
                                             (coe v12)))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_588 v7 v8 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_132 v13
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RApp'45'In_11526
                           (coe v0) (coe v12) (coe v13) (coe v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_600 v6 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RApp'45'apply_11564
                    (coe v0) (coe v11) (coe v6) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_612 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v12 v13
                      -> coe
                           du_completeness'45'gap'45'inl'45'app'45'check'45'eq_2382 (coe v0)
                           (coe v11) (coe v12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_624 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v12 v13
                      -> coe
                           du_completeness'45'gap'45'inr'45'app'45'check'45'eq_2430 (coe v0)
                           (coe v11) (coe v13)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_634 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> coe
                    du_completeness'45'gap'45'initial'45'app'45'check'45'eq_2476
                    (coe v0) (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_646 v9
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v10 v11 v12
               -> coe
                    du_subsume'45'complete_4872 (coe v0) (coe v1) (coe v10) (coe v12)
                    (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_662 v7 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> coe
                    d_completeness'45'gap'45'arg'45'driven'45'app'45'check_3002 v0 v14
                    v15 v7 v2 v9 v10 erased v12 v13
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_674 v7 v8 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v15
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RVar'45'poly_13024
                    (coe v0) (coe v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.subsume-complete
d_subsume'45'complete_4872 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_subsume'45'complete_4872 v0 v1 v2 v3 ~v4 v5
  = du_subsume'45'complete_4872 v0 v1 v2 v3 v5
du_subsume'45'complete_4872 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_subsume'45'complete_4872 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_520 v10
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'id_344
               -> coe
                    d_morph'45'complete_4510 (coe v0)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                       (coe ("id" :: Data.Text.Text)))
                    (coe v2) (coe v2) (coe MAlonzo.Code.Once.Type.C_eff_36)
                    (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'id_344)
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'fst_354
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__126 v17 v18
                      -> coe
                           d_morph'45'complete_4510 (coe v0)
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                              (coe ("fst" :: Data.Text.Text)))
                           (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v3) (coe v18))
                           (coe v3) (coe MAlonzo.Code.Once.Type.C_eff_36)
                           (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'fst_354)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'snd_364
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__126 v17 v18
                      -> coe
                           d_morph'45'complete_4510 (coe v0)
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                              (coe ("snd" :: Data.Text.Text)))
                           (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v17) (coe v3))
                           (coe v3) (coe MAlonzo.Code.Once.Type.C_eff_36)
                           (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'snd_364)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'terminal_372
               -> coe
                    d_morph'45'complete_4510 (coe v0)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                       (coe ("terminal" :: Data.Text.Text)))
                    (coe v2) (coe MAlonzo.Code.Once.Type.C_Unit_122)
                    (coe MAlonzo.Code.Once.Type.C_eff_36)
                    (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'terminal_372)
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'initial_380
               -> coe
                    d_morph'45'complete_4510 (coe v0)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                       (coe ("initial" :: Data.Text.Text)))
                    (coe MAlonzo.Code.Once.Type.C_Void_124) (coe v3)
                    (coe MAlonzo.Code.Once.Type.C_eff_36)
                    (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'initial_380)
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inl_390
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v17 v18
                      -> coe
                           d_morph'45'complete_4510 (coe v0)
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                              (coe ("inl" :: Data.Text.Text)))
                           (coe v2)
                           (coe MAlonzo.Code.Once.Type.C__'43'__128 (coe v2) (coe v18))
                           (coe MAlonzo.Code.Once.Type.C_eff_36)
                           (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inl_390)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inr_400
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v17 v18
                      -> coe
                           d_morph'45'complete_4510 (coe v0)
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                              (coe ("inr" :: Data.Text.Text)))
                           (coe v2)
                           (coe MAlonzo.Code.Once.Type.C__'43'__128 (coe v17) (coe v2))
                           (coe MAlonzo.Code.Once.Type.C_eff_36)
                           (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inr_400)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'compose_416 v15 v19 v20
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v21 v22
                      -> case coe v21 of
                           MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v23 v24
                             -> coe
                                  du_compose'45'eff'45'complete_4600 (coe v0) (coe v24) (coe v22)
                                  (coe v2) (coe v15) (coe v3) (coe v19) (coe v20)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'case_432 v18 v19
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v20 v21
                      -> case coe v20 of
                           MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v22 v23
                             -> case coe v2 of
                                  MAlonzo.Code.Once.Type.C__'43'__128 v24 v25
                                    -> coe
                                         d_case'45'eff'45'complete_4620 (coe v0) (coe v23) (coe v21)
                                         (coe v24) (coe v25) (coe v3) (coe v18) (coe v19)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'pair_446 v17 v18
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v19 v20
                      -> case coe v19 of
                           MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v21 v22
                             -> case coe v3 of
                                  MAlonzo.Code.Once.Type.C__'42'__126 v23 v24
                                    -> coe
                                         d_pair'45'eff'45'complete_4530 (coe v0) (coe v22) (coe v20)
                                         (coe v2) (coe v23) (coe v24) (coe v17) (coe v18)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'curry_458 v16
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
                      -> case coe v3 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v19 v20 v21
                             -> coe
                                  d_curry'45'eff'45'complete_4548 (coe v0) (coe v18) (coe v2)
                                  (coe v19) (coe v21) (coe v16)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'cata_472 v16 v18
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v19 v20
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C_μ'45'type_132 v21
                             -> coe
                                  du_cata'45'eff'45'complete_4638 (coe v0) (coe v20) (coe v21)
                                  (coe v3) (coe v16) (coe v18)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_484 v16
               -> coe
                    d_morph'45'complete_4510 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe MAlonzo.Code.Once.Type.C_eff_36)
                    (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_484 v16)
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named_496
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v19
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RVar'45'eff_13908
                           (coe v0) (coe v19) (coe v2) (coe v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named'45'resolved_508
               -> coe
                    du_embedOrSubsume'45'lifts_2522 (coe v2) (coe v3)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1658 (coe v0)
                       (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_530 v9
        -> coe
             du_iFromInferEff_4746 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_548 v11 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v15 v16
               -> coe
                    du_check'45'complete'45'RLam'45'eff_1488 (coe v0) (coe v15)
                    (coe v16) (coe v2) (coe v11) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_560 v10
        -> coe du_gd'45'complete_4826 (coe v0) (coe v1) (coe v3) (coe v10)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_600 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    du_iFromInferEff_4746 (coe v0)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                          (coe ("apply" :: Data.Text.Text)))
                       (coe v12))
                    (coe v2) (coe v3)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_250
                       v7 v9 v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_634 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RApp'45'initial'45'eff_14016
                    (coe v0) (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_662 v8 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> coe
                    d_completeness'45'gap'45'arg'45'driven'45'app'45'check'45'eff_3026
                    v0 v15 v16 v8 v2 v3 v10 v11 erased v13 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_674 v8 v9 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v16
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RVar'45'poly_13024
                    (coe v0) (coe v16)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
