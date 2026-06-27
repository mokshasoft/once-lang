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
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Surface.Thinning
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.MorphComplete
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

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
                                 (MAlonzo.Code.Once.TypeCheck.Elaborate.d_ext'45'arrow'45'info_1728
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
                                 (MAlonzo.Code.Once.TypeCheck.Elaborate.d_ext'45'resolved'45'info_1740
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
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v6 v7 v8 v9 v10
                  -> let v11
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
                               (coe v0) (coe v2) in
                     coe
                       (case coe v11 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                            -> case coe v12 of
                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v14 v15 v16 v17 v18
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
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v5 v6 v7 v8 v9
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
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_1442
              (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_320 v6 v7 v8 v9
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
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
              (coe v0) (coe v2) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v7 v8 v9 v10 v11
                  -> let v12
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
                               (coe
                                  MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_234 (coe v0)
                                  (coe v1) (coe v7))
                               (coe v3) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                            -> case coe v13 of
                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v15 v16 v17 v18 v19
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
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v5 v6 v7 v8 v9
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
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v5 v6 v7 v8 v9
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
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v5 v6 v7 v8 v9
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
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v5 v6 v7 v8 v9
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
-- Once.TypeCheck.Completeness.infer-complete-RApp-arr
d_infer'45'complete'45'RApp'45'arr_674 ::
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
d_infer'45'complete'45'RApp'45'arr_674 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 ~v8
  = du_infer'45'complete'45'RApp'45'arr_674 v0 v1
du_infer'45'complete'45'RApp'45'arr_674 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'arr_674 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v5 v6 v7 v8 v9
                  -> case coe v5 of
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v10 v11 v12
                         -> case coe v11 of
                              MAlonzo.Code.Once.Type.C_mk'45'kind_50 v13 v14
                                -> coe
                                     seq (coe v13)
                                     (coe
                                        seq (coe v14)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe MAlonzo.Code.Once.Surface.Syntax.C_arr''_496 v7)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                              (coe addInt (coe (1 :: Integer)) (coe v8))
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v9) erased))))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.infer-complete-RApp-apply
d_infer'45'complete'45'RApp'45'apply_714 ::
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
d_infer'45'complete'45'RApp'45'apply_714 v0 v1 v2 ~v3 ~v4 ~v5 ~v6
                                         ~v7 ~v8
  = du_infer'45'complete'45'RApp'45'apply_714 v0 v1 v2
du_infer'45'complete'45'RApp'45'apply_714 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'apply_714 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v6 v7 v8 v9 v10
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
                                                      = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__220
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
                                                                         MAlonzo.Code.Once.Surface.Syntax.C_app_224
                                                                         (MAlonzo.Code.Once.Surface.Syntax.d_zeroUsage_70
                                                                            (coe
                                                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_186
                                                                               (coe v0)))
                                                                         v7
                                                                         (coe
                                                                            MAlonzo.Code.Once.Type.C__'42'__126
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.d__'8658'__150
                                                                               (coe v2) (coe v15))
                                                                            (coe v2))
                                                                         (coe
                                                                            MAlonzo.Code.Once.Type.C_Many_10)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Surface.Thinning.du_weakenFromEmpty_1142
                                                                            (coe
                                                                               MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190
                                                                               (coe v0))
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Type.C__'42'__126
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Type.d__'8658'__150
                                                                                     (coe v2)
                                                                                     (coe v15))
                                                                                  (coe v2))
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Type.C_Many_10)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Type.C_pure_34))
                                                                               (coe v15))
                                                                            (coe
                                                                               MAlonzo.Code.Once.TypeCheck.Elaborate.d_specApply_496
                                                                               (coe v2) (coe v15)))
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
d_infer'45'complete'45'RVar'45'local_780 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RVar'45'local_780 v0 v1 ~v2 ~v3 v4 ~v5 ~v6
  = du_infer'45'complete'45'RVar'45'local_780 v0 v1 v4
du_infer'45'complete'45'RVar'45'local_780 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RVar'45'local_780 v0 v1 v2
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
d_helper_840 ::
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
d_helper_840 = erased
-- Once.TypeCheck.Completeness.infer-complete-RVar-import
d_infer'45'complete'45'RVar'45'import_854 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RVar'45'import_854 v0 v1 ~v2 ~v3 ~v4 ~v5
  = du_infer'45'complete'45'RVar'45'import_854 v0 v1
du_infer'45'complete'45'RVar'45'import_854 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RVar'45'import_854 v0 v1
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
d_helperLoc_908 ::
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
d_helperLoc_908 = erased
-- Once.TypeCheck.Completeness._.helperImp
d_helperImp_914 ::
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
d_helperImp_914 = erased
-- Once.TypeCheck.Completeness.infer-complete-RBinOp-arith
d_infer'45'complete'45'RBinOp'45'arith_948 ::
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
d_infer'45'complete'45'RBinOp'45'arith_948 v0 v1 ~v2 v3 v4 ~v5 ~v6
                                           ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14
  = du_infer'45'complete'45'RBinOp'45'arith_948 v0 v1 v3 v4
du_infer'45'complete'45'RBinOp'45'arith_948 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RBinOp'45'arith_948 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
        -> let v4
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v15 v16 v17 v18 v19
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v15 v16 v17 v18 v19
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v15 v16 v17 v18 v19
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v15 v16 v17 v18 v19
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v15 v16 v17 v18 v19
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
d_infer'45'complete'45'RBinOp'45'cmp_1172 ::
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
d_infer'45'complete'45'RBinOp'45'cmp_1172 v0 v1 ~v2 v3 v4 ~v5 ~v6
                                          ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14
  = du_infer'45'complete'45'RBinOp'45'cmp_1172 v0 v1 v3 v4
du_infer'45'complete'45'RBinOp'45'cmp_1172 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RBinOp'45'cmp_1172 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpLt_18
        -> let v4
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v15 v16 v17 v18 v19
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v15 v16 v17 v18 v19
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v15 v16 v17 v18 v19
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v15 v16 v17 v18 v19
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v15 v16 v17 v18 v19
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v15 v16 v17 v18 v19
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
d_decideLeq'45'just_1408 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_decideLeq'45'just_1408 v0 v1 ~v2
  = du_decideLeq'45'just_1408 v0 v1
du_decideLeq'45'just_1408 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_decideLeq'45'just_1408 v0 v1
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
-- Once.TypeCheck.Completeness.check-complete-RLam
d_check'45'complete'45'RLam_1438 ::
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
d_check'45'complete'45'RLam_1438 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9
                                 ~v10 ~v11 ~v12
  = du_check'45'complete'45'RLam_1438 v0 v1 v2 v3 v4 v5 v6
du_check'45'complete'45'RLam_1438 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_check'45'complete'45'RLam_1438 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_1442
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_234 (coe v0)
                 (coe v1) (coe v3))
              (coe v2) (coe v6) in
    coe
      (case coe v7 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
           -> case coe v8 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_320 v10 v11 v12 v13
                  -> coe
                       seq (coe v10)
                       (let v14
                              = MAlonzo.Code.Once.TypeCheck.Elaborate.d_decideLeq_1260
                                  (coe v5) (coe v4) in
                        coe
                          (let v15 = coe du_decideLeq'45'just_1408 (coe v5) (coe v4) in
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
-- Once.TypeCheck.Completeness.infer-complete-RDestruct
d_infer'45'complete'45'RDestruct_1554 ::
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
d_infer'45'complete'45'RDestruct_1554 v0 v1 v2 v3 v4 v5 ~v6 ~v7 ~v8
                                      ~v9 ~v10 ~v11 v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21
                                      ~v22 ~v23 ~v24 ~v25
  = du_infer'45'complete'45'RDestruct_1554 v0 v1 v2 v3 v4 v5 v12
du_infer'45'complete'45'RDestruct_1554 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RDestruct_1554 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
              (coe v0) (coe v1) in
    coe
      (case coe v7 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
           -> case coe v8 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v10 v11 v12 v13 v14
                  -> case coe v10 of
                       MAlonzo.Code.Once.Type.C__'43'__128 v15 v16
                         -> let v17
                                  = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_234
                                         (coe v0) (coe v2) (coe v15))
                                      (coe v3) in
                            coe
                              (case coe v17 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                   -> case coe v18 of
                                        MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v20 v21 v22 v23 v24
                                          -> case coe v21 of
                                               MAlonzo.Code.Once.Surface.Syntax.C__'8759'__66 v26 v27
                                                 -> let v28
                                                          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
                                                              (coe
                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_234
                                                                 (coe v0) (coe v4) (coe v16))
                                                              (coe v5) in
                                                    coe
                                                      (case coe v28 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v29 v30
                                                           -> case coe v29 of
                                                                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v31 v32 v33 v34 v35
                                                                  -> case coe v32 of
                                                                       MAlonzo.Code.Once.Surface.Syntax.C__'8759'__66 v37 v38
                                                                         -> let v39
                                                                                  = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__220
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
d_infer'45'complete'45'RApp'45'generic_1752 ::
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
d_infer'45'complete'45'RApp'45'generic_1752 v0 v1 v2 v3 ~v4 v5 ~v6
                                            ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16
  = du_infer'45'complete'45'RApp'45'generic_1752 v0 v1 v2 v3 v5
du_infer'45'complete'45'RApp'45'generic_1752 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'generic_1752 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
              (coe v0) (coe v1) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> case coe v6 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v8 v9 v10 v11 v12
                  -> let v13
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_1442
                               (coe v0) (coe v2) (coe v3) in
                     coe
                       (case coe v13 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                            -> case coe v14 of
                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_320 v16 v17 v18 v19
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
d_viewBridge_1764 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_AppHeadView_964 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_viewBridge_1764 = erased
-- Once.TypeCheck.Completeness.otherBridge
d_otherBridge_1776 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Classify.T_PolyBuiltinApp_806 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_otherBridge_1776 = erased
-- Once.TypeCheck.Completeness.infer-complete-RApp-eff
d_infer'45'complete'45'RApp'45'eff_1880 ::
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
d_infer'45'complete'45'RApp'45'eff_1880 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7
                                        ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15
  = du_infer'45'complete'45'RApp'45'eff_1880 v0 v1 v2 v3
du_infer'45'complete'45'RApp'45'eff_1880 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'eff_1880 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1434
              (coe v0) (coe v1) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v7 v8 v9 v10 v11
                  -> let v12
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_1442
                               (coe v0) (coe v2) (coe v3) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                            -> case coe v13 of
                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_320 v15 v16 v17 v18
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
d_checkElab'45'fallback'45'RVar_1966 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar_1966 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_checkElab'45'fallback'45'RVar_1966 v0 v1 v2
du_checkElab'45'fallback'45'RVar_1966 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar_1966 v0 v1 v2
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
                               (coe MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'id_1752) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'id_1752
                            -> let v7
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1546
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
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v10 v11 v12 v13 v14
                                             -> let v15
                                                      = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__220
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
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'fst_1754
                            -> let v7
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1546
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
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v10 v11 v12 v13 v14
                                             -> let v15
                                                      = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__220
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
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'snd_1756
                            -> let v7
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1546
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
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v10 v11 v12 v13 v14
                                             -> let v15
                                                      = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__220
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
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'terminal_1758
                            -> let v7
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1546
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
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v10 v11 v12 v13 v14
                                             -> let v15
                                                      = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__220
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
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'initial_1760
                            -> let v7
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1546
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
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v10 v11 v12 v13 v14
                                             -> let v15
                                                      = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__220
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
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inl_1762
                            -> let v7
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1546
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
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v10 v11 v12 v13 v14
                                             -> let v15
                                                      = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__220
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
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inr_1764
                            -> let v7
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1546
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
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v10 v11 v12 v13 v14
                                             -> let v15
                                                      = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__220
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
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'arr_1766
                            -> let v7
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1546
                                         (coe v0) (coe ("arr" :: Data.Text.Text))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_186
                                               (coe v0))
                                            (coe ("arr" :: Data.Text.Text))
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
                                            (coe ("arr" :: Data.Text.Text))) in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                      -> case coe v8 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v10 v11 v12 v13 v14
                                             -> let v15
                                                      = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__220
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
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'other_1770
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
                                                                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296
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
                                                            MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v14 v15 v16 v17 v18
                                                              -> let v19
                                                                       = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__220
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
                                                              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1546
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
                                                             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v14 v15 v16 v17 v18
                                                               -> let v19
                                                                        = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__220
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
                                                       MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'fst_1754)
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
                                                                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'snd_1756)
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
                                                                                               MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'terminal_1758)
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
                                                                                                                   MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'initial_1760)
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
                                                                                                                                       MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inl_1762)
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
                                                                                                                                                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inr_1764)
                                                                                                                                                 else coe
                                                                                                                                                        seq
                                                                                                                                                        (coe
                                                                                                                                                           v23)
                                                                                                                                                        (let v24
                                                                                                                                                               = coe
                                                                                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                   erased
                                                                                                                                                                   (\ v24 ->
                                                                                                                                                                      coe
                                                                                                                                                                        MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                        (coe
                                                                                                                                                                           v1))
                                                                                                                                                                   (coe
                                                                                                                                                                      MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                      (coe
                                                                                                                                                                         v1)
                                                                                                                                                                      (coe
                                                                                                                                                                         ("arr"
                                                                                                                                                                          ::
                                                                                                                                                                          Data.Text.Text))) in
                                                                                                                                                         coe
                                                                                                                                                           (case coe
                                                                                                                                                                   v24 of
                                                                                                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v25 v26
                                                                                                                                                                -> if coe
                                                                                                                                                                        v25
                                                                                                                                                                     then coe
                                                                                                                                                                            seq
                                                                                                                                                                            (coe
                                                                                                                                                                               v26)
                                                                                                                                                                            (coe
                                                                                                                                                                               MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'arr_1766)
                                                                                                                                                                     else coe
                                                                                                                                                                            seq
                                                                                                                                                                            (coe
                                                                                                                                                                               v26)
                                                                                                                                                                            (coe
                                                                                                                                                                               MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'other_1770)
                                                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                      _ -> MAlonzo.RTE.mazUnreachableError)) in
                      coe
                        (case coe v6 of
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'id_1752
                             -> let v7
                                      = coe
                                          MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1546
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
                                            MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v10 v11 v12 v13 v14
                                              -> let v15
                                                       = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__220
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
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'fst_1754
                             -> let v7
                                      = coe
                                          MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1546
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
                                            MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v10 v11 v12 v13 v14
                                              -> let v15
                                                       = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__220
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
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'snd_1756
                             -> let v7
                                      = coe
                                          MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1546
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
                                            MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v10 v11 v12 v13 v14
                                              -> let v15
                                                       = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__220
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
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'terminal_1758
                             -> let v7
                                      = coe
                                          MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1546
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
                                            MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v10 v11 v12 v13 v14
                                              -> let v15
                                                       = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__220
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
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'initial_1760
                             -> let v7
                                      = coe
                                          MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1546
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
                                            MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v10 v11 v12 v13 v14
                                              -> let v15
                                                       = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__220
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
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inl_1762
                             -> let v7
                                      = coe
                                          MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1546
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
                                            MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v10 v11 v12 v13 v14
                                              -> let v15
                                                       = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__220
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
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inr_1764
                             -> let v7
                                      = coe
                                          MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1546
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
                                            MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v10 v11 v12 v13 v14
                                              -> let v15
                                                       = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__220
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
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'arr_1766
                             -> let v7
                                      = coe
                                          MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1546
                                          (coe v0) (coe ("arr" :: Data.Text.Text))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_size_186
                                                (coe v0))
                                             (coe ("arr" :: Data.Text.Text))
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
                                             (coe ("arr" :: Data.Text.Text))) in
                                coe
                                  (case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                       -> case coe v8 of
                                            MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v10 v11 v12 v13 v14
                                              -> let v15
                                                       = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__220
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
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'other_1770
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
                                                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296
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
                                                             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v14 v15 v16 v17 v18
                                                               -> let v19
                                                                        = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__220
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
                                                               MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1546
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
                                                              MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_296 v14 v15 v16 v17 v18
                                                                -> let v19
                                                                         = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__220
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
d_completeness'45'gap'45'inl'45'app'45'check'45'eq_2380 ::
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
d_completeness'45'gap'45'inl'45'app'45'check'45'eq_2380 v0 v1 v2
                                                        ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_completeness'45'gap'45'inl'45'app'45'check'45'eq_2380 v0 v1 v2
du_completeness'45'gap'45'inl'45'app'45'check'45'eq_2380 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_completeness'45'gap'45'inl'45'app'45'check'45'eq_2380 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_1442
              (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_320 v6 v7 v8 v9
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
d_completeness'45'gap'45'inr'45'app'45'check'45'eq_2428 ::
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
d_completeness'45'gap'45'inr'45'app'45'check'45'eq_2428 v0 v1 ~v2
                                                        v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_completeness'45'gap'45'inr'45'app'45'check'45'eq_2428 v0 v1 v3
du_completeness'45'gap'45'inr'45'app'45'check'45'eq_2428 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_completeness'45'gap'45'inr'45'app'45'check'45'eq_2428 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_1442
              (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_320 v6 v7 v8 v9
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
d_completeness'45'gap'45'initial'45'app'45'check'45'eq_2474 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_completeness'45'gap'45'initial'45'app'45'check'45'eq_2474 v0 v1
                                                            ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_completeness'45'gap'45'initial'45'app'45'check'45'eq_2474
      v0 v1
du_completeness'45'gap'45'initial'45'app'45'check'45'eq_2474 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_completeness'45'gap'45'initial'45'app'45'check'45'eq_2474 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_1442
              (coe v0) (coe v1) (coe MAlonzo.Code.Once.Type.C_Void_124) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_320 v5 v6 v7 v8
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
-- Once.TypeCheck.Completeness.completeness-gap-arr-app-check-eq
d_completeness'45'gap'45'arr'45'app'45'check'45'eq_2518 ::
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
d_completeness'45'gap'45'arr'45'app'45'check'45'eq_2518 v0 v1 v2 v3
                                                        ~v4 ~v5 ~v6 ~v7 ~v8
  = du_completeness'45'gap'45'arr'45'app'45'check'45'eq_2518
      v0 v1 v2 v3
du_completeness'45'gap'45'arr'45'app'45'check'45'eq_2518 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_completeness'45'gap'45'arr'45'app'45'check'45'eq_2518 v0 v1 v2
                                                         v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_1442
              (coe v0) (coe v1)
              (coe
                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v2)
                 (coe
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                    (coe MAlonzo.Code.Once.Type.C_pure_34))
                 (coe v3)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_320 v7 v8 v9 v10
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Once.Surface.Syntax.C_arr''_496 v8)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe addInt (coe (1 :: Integer)) (coe v9))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10) erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.completeness-gap-arr-check
d_completeness'45'gap'45'arr'45'check_2560
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.Completeness.completeness-gap-arr-check"
-- Once.TypeCheck.Completeness.completeness-gap-apply-check
d_completeness'45'gap'45'apply'45'check_2578
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.Completeness.completeness-gap-apply-check"
-- Once.TypeCheck.Completeness.completeness-gap-arg-driven-app-check
d_completeness'45'gap'45'arg'45'driven'45'app'45'check_2600
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.Completeness.completeness-gap-arg-driven-app-check"
-- Once.TypeCheck.Completeness.infer-complete
d_infer'45'complete_2616 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete_2616 v0 v1 v2 ~v3 v4
  = du_infer'45'complete_2616 v0 v1 v2 v4
du_infer'45'complete_2616 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete_2616 v0 v1 v2 v3
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
                    du_infer'45'complete'45'RVar'45'local_780 (coe v0) (coe v11)
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
                    du_infer'45'complete'45'RVar'45'import_854 (coe v0) (coe v10)
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
                    du_infer'45'complete'45'RDestruct_1554 (coe v0) (coe v21) (coe v22)
                    (coe v23) (coe v24) (coe v25) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_180 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_60 v13 v14 v15
               -> coe
                    du_infer'45'complete'45'RBinOp'45'arith_948 (coe v0) (coe v13)
                    (coe v14) (coe v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_194 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_60 v13 v14 v15
               -> coe
                    du_infer'45'complete'45'RBinOp'45'cmp_1172 (coe v0) (coe v13)
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arr'45'app'45'infer_250 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe du_infer'45'complete'45'RApp'45'arr_674 (coe v0) (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_262 v6 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    du_infer'45'complete'45'RApp'45'apply_714 (coe v0) (coe v11)
                    (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_280 v7 v9 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> coe
                    du_infer'45'complete'45'RApp'45'generic_1752 (coe v0) (coe v15)
                    (coe v16) (coe v7) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_296 v7 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> coe
                    du_infer'45'complete'45'RApp'45'eff_1880 (coe v0) (coe v14)
                    (coe v15) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.pair-lit-check-complete
d_pair'45'lit'45'check'45'complete_2638
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.Completeness.pair-lit-check-complete"
-- Once.TypeCheck.Completeness.nothing≢just
d_nothing'8802'just_2648 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  () -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_nothing'8802'just_2648 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_nothing'8802'just_2648
du_nothing'8802'just_2648 :: AgdaAny
du_nothing'8802'just_2648 = MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.checkG-just
d_checkG'45'just_2664 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkG'45'just_2664 v0 v1 v2 ~v3 v4
  = du_checkG'45'just_2664 v0 v1 v2 v4
du_checkG'45'just_2664 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkG'45'just_2664 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'int_302
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Once.Surface.Elaborate.du_intLit_8 (coe v6))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'int_302) erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'terminal_306
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
                         -> coe seq (coe v10) (coe du_nothing'8802'just_2648)
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> let v8
                           = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                               (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194 (coe v0))
                               (coe ("terminal" :: Data.Text.Text)) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                            -> coe du_nothing'8802'just_2648
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe MAlonzo.Code.Once.IR.C_terminal_74)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'terminal_306)
                                    erased)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'pair_318 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__126 v13 v14
                      -> let v15
                               = coe
                                   du_checkG'45'just_2664 (coe v0) (coe v11) (coe v13) (coe v9) in
                         coe
                           (let v16
                                  = coe
                                      du_checkG'45'just_2664 (coe v0) (coe v12) (coe v14)
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
                                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'pair_318
                                                                   v19 v23)
                                                                erased)
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inl_328 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v11 v12
                      -> let v13
                               = coe
                                   du_checkG'45'just_2664 (coe v0) (coe v10) (coe v11) (coe v8) in
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
                                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inl_328
                                                  v16)
                                               erased)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inr_338 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v11 v12
                      -> let v13
                               = coe
                                   du_checkG'45'just_2664 (coe v0) (coe v10) (coe v12) (coe v8) in
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
                                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inr_338
                                                  v16)
                                               erased)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'In_348 v7 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_132 v12
                      -> let v13
                               = coe
                                   du_checkG'45'just_2664 (coe v0) (coe v11)
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
                                                            MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'In_348
                                                            v15 v18)
                                                         erased)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                   -> coe du_nothing'8802'just_2648
                                 _ -> MAlonzo.RTE.mazUnreachableError))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.gd-complete
d_gd'45'complete_2680 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_gd'45'complete_2680 v0 v1 v2 ~v3 v4
  = du_gd'45'complete_2680 v0 v1 v2 v4
du_gd'45'complete_2680 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_gd'45'complete_2680 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'int_302
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
                          erased))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'terminal_306
        -> coe
             MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RVar'45'terminal_11466
             (coe v0)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'pair_318 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__126 v13 v14
                      -> let v15
                               = coe
                                   MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkG_652 (coe v0)
                                   (coe v11) (coe v13) in
                         coe
                           (let v16
                                  = coe
                                      MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkG_652 (coe v0)
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
                                                                      erased)))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> coe du_nothing'8802'just_2648
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> coe du_nothing'8802'just_2648))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inl_328 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v11 v12
                      -> let v13
                               = coe
                                   MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkG_652 (coe v0)
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
                                                     erased)))
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
                                                         erased))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                       -> coe du_nothing'8802'just_2648
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inr_338 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v11 v12
                      -> let v13
                               = coe
                                   MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkG_652 (coe v0)
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
                                                     erased)))
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
                                                         erased))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                       -> coe du_nothing'8802'just_2648
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'In_348 v7 v9
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
                                             MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkG_652
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
                                                               erased)))
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
                                                                   erased))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                 -> let v16
                                                          = coe
                                                              du_checkG'45'just_2664 (coe v0)
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
                                                                (coe du_nothing'8802'just_2648)
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                -> let v14 = coe du_nothing'8802'just_2648 in
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
d_check'45'complete_2696 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_check'45'complete_2696 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_540 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v11 v12 v13
               -> case coe v12 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v14 v15
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.MorphComplete.d_morph'45'complete_1038
                           (coe v0) (coe v1) (coe v11) (coe v13) (coe v15) (coe v10)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_550 v9
        -> case coe v9 of
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_30
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v12
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab'45'fallback'45'RInt_9978
                           (coe v0) (coe v12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'str_36
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_56 v12
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab'45'fallback'45'RStringLit_10008
                           (coe v0) (coe v12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_40
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab'45'fallback'45'RUnit_10036
                    (coe v0)
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_44
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElab'45'fallback'45'RVar'45'unit_11050
                    (coe v0)
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_56 v14
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v17
                      -> coe
                           du_checkElab'45'fallback'45'RVar_1966 (coe v0) (coe v17) (coe v2)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_66
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v15 v16
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RQualified_10072
                           (coe v0) (coe v15) (coe v16)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_74
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v14
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RResolved_10230
                           (coe v0) (coe v14)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_82
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v16
                      -> coe
                           du_checkElab'45'fallback'45'RVar_1966 (coe v0) (coe v16) (coe v2)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_92 v14
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_58 v15 v16
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RAnnot_10374
                           (coe v0) (coe v15) (coe v2)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_108 v15 v16 v17 v18
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v19 v20
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'42'__126 v21 v22
                             -> coe
                                  d_pair'45'lit'45'check'45'complete_2638 v0 v19 v20 v21 v22 v15 v16
                                  (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_550 v17)
                                  (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_550 v18)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_116 v13
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_62 v15
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RUnaryOp_10904
                           (coe v0) (coe v15)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_136 v14 v16 v17 v18 v19 v20
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v21 v22 v23
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RLet_10522
                           (coe v0) (coe v21) (coe v22) (coe v23)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_166 v16 v17 v19 v20 v21 v22 v23 v24 v25 v26
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v27 v28 v29 v30 v31
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RDestruct_10702
                           (coe v0) (coe v27) (coe v28) (coe v29) (coe v30) (coe v31)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_180 v14 v15 v17 v18
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_60 v19 v20 v21
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RBinOp_13934
                           (coe v0) (coe v19) (coe v20) (coe v21)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_194 v14 v15 v17 v18
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_60 v19 v20 v21
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RBinOp_13934
                           (coe v0) (coe v19) (coe v20) (coe v21)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_204 v13 v14
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RApp'45'id_13550
                           (coe v0) (coe v16) (coe v2)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_216 v13 v14 v15
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RApp'45'fst_13620
                           (coe v0) (coe v17) (coe v2)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_228 v12 v14 v15
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RApp'45'snd_13690
                           (coe v0) (coe v17) (coe v2)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_238 v12 v13 v14
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RApp'45'terminal_13860
                           (coe v0) (coe v16) (coe MAlonzo.Code.Once.Type.C_Unit_122)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arr'45'app'45'infer_250 v15
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v18 v19 v20
                             -> coe
                                  d_completeness'45'gap'45'arr'45'check_2560 v0 v17 v18 v20 v3 v15
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_262 v12 v14 v15
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
                      -> coe
                           d_completeness'45'gap'45'apply'45'check_2578 v0 v17 v12 v2 v14 v15
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_280 v13 v15 v16 v17 v19 v20
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v21 v22
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RApp'45'generic_13776
                           (coe v0) (coe v21) (coe v22) (coe v2)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_296 v13 v15 v16 v18 v19
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v20 v21
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v22 v23 v24
                             -> coe
                                  MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RApp'45'generic_13776
                                  (coe v0) (coe v20) (coe v21)
                                  (coe
                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                     (coe MAlonzo.Code.Once.Type.C_Unit_122)
                                     (coe
                                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                                        (coe MAlonzo.Code.Once.Type.C_eff_36))
                                     (coe v24))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_568 v11 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v15 v16
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v17 v18 v19
                      -> case coe v18 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v20 v21
                             -> coe
                                  du_check'45'complete'45'RLam_1438 (coe v0) (coe v15) (coe v16)
                                  (coe v17) (coe v20) (coe v11) (coe v19)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_578 v9
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v10 v11 v12
               -> coe du_gd'45'complete_2680 (coe v0) (coe v1) (coe v12) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_594 v10 v11 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__126 v16 v17
                      -> coe
                           d_pair'45'lit'45'check'45'complete_2638 v0 v14 v15 v16 v17 v10 v11
                           v12 v13
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_606 v8 v9 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_132 v14
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RApp'45'In_11882
                           (coe v0) (coe v13) (coe v14) (coe v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_618 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RApp'45'apply_11968
                    (coe v0) (coe v12) (coe v7) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_630 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v13 v14
                      -> coe
                           du_completeness'45'gap'45'inl'45'app'45'check'45'eq_2380 (coe v0)
                           (coe v12) (coe v13)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_642 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v13 v14
                      -> coe
                           du_completeness'45'gap'45'inr'45'app'45'check'45'eq_2428 (coe v0)
                           (coe v12) (coe v14)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_652 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    du_completeness'45'gap'45'initial'45'app'45'check'45'eq_2474
                    (coe v0) (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arr'45'app'45'check_664 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v13 v14 v15
                      -> coe
                           du_completeness'45'gap'45'arr'45'app'45'check'45'eq_2518 (coe v0)
                           (coe v12) (coe v13) (coe v15)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_680 v8 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> coe
                    d_completeness'45'gap'45'arg'45'driven'45'app'45'check_2600 v0 v15
                    v16 v8 v2 v10 v11 erased v13 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_692 v8 v9 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v16
               -> coe
                    MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElab'45'fallback'45'RVar'45'poly_13414
                    (coe v0) (coe v16) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
