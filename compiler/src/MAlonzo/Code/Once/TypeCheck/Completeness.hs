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
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Functor.Decide
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.ElaborateProofs
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.TypeCheck.Completeness.infer-complete-RInt
d_infer'45'complete'45'RInt_16 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RInt_16 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_int_184 v1)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
            erased))
-- Once.TypeCheck.Completeness.infer-complete-RStringLit
d_infer'45'complete'45'RStringLit_30 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RStringLit_30 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_str_190 v1)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
            erased))
-- Once.TypeCheck.Completeness.infer-complete-RUnit
d_infer'45'complete'45'RUnit_42 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RUnit_42 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_152)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
            erased))
-- Once.TypeCheck.Completeness.infer-complete-RVar-unit
d_infer'45'complete'45'RVar'45'unit_52 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RVar'45'unit_52 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_152)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe
               MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
            erased))
-- Once.TypeCheck.Completeness.infer-complete-RQualified
d_infer'45'complete'45'RQualified_68 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RQualified_68 v0 v1 v2 v3 ~v4 v5
  = du_infer'45'complete'45'RQualified_68 v0 v1 v2 v3 v5
du_infer'45'complete'45'RQualified_68 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RQualified_68 v0 v1 v2 v3 v4
  = coe du_go_130 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Once.TypeCheck.Completeness._.helper
d_helper_90 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helper_90 = erased
-- Once.TypeCheck.Completeness._.helperArr
d_helperArr_108 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helperArr_108 = erased
-- Once.TypeCheck.Completeness._.helperVal
d_helperVal_118 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helperVal_118 = erased
-- Once.TypeCheck.Completeness._.go
d_go_130 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_130 v0 v1 v2 ~v3 ~v4 ~v5 v6 v7 ~v8 = du_go_130 v0 v1 v2 v6 v7
du_go_130 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_130 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Type.C_Unit_118
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384
                (MAlonzo.Code.Once.CanonicalName.d_bare_12
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("." :: Data.Text.Text) v1)))
                (coe
                   MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230
                   (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C_Void_120
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384
                (MAlonzo.Code.Once.CanonicalName.d_bare_12
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("." :: Data.Text.Text) v1)))
                (coe
                   MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230
                   (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Void_204)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C__'42'__122 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384
                (MAlonzo.Code.Once.CanonicalName.d_bare_12
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("." :: Data.Text.Text) v1)))
                (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63''45'complete_152
                      (coe v3) (coe v4))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C__'43'__124 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384
                (MAlonzo.Code.Once.CanonicalName.d_bare_12
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("." :: Data.Text.Text) v1)))
                (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63''45'complete_152
                      (coe v3) (coe v4))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v5 v6 v7
        -> case coe v6 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v8 v9
               -> case coe v8 of
                    MAlonzo.Code.Once.Type.C_Zero_6
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384
                              (MAlonzo.Code.Once.CanonicalName.d_bare_12
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                       ("." :: Data.Text.Text) v1)))
                              (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63''45'complete_152
                                    (coe v3) (coe v4))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                    (coe v0))
                                 erased))
                    MAlonzo.Code.Once.Type.C_One_8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384
                              (MAlonzo.Code.Once.CanonicalName.d_bare_12
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                       ("." :: Data.Text.Text) v1)))
                              (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63''45'complete_152
                                    (coe v3) (coe v4))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                    (coe v0))
                                 erased))
                    MAlonzo.Code.Once.Type.C_Many_10
                      -> case coe v4 of
                           MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_238 v13 v14
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                     (coe
                                        MAlonzo.Code.Once.IR.C_SigOp_156 (coe v5) (coe v7)
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.d_ext'45'arrow'45'info_1978
                                           (coe v5) (coe v7) (coe v0) (coe v2) (coe v1) (coe v9)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                              (coe
                                                 MAlonzo.Code.Once.Functor.Decide.d_isBaseType'63''45'complete_90
                                                 (coe v5) (coe v13)))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                              (coe
                                                 MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63''45'complete_152
                                                 (coe v7) (coe v14))))))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe (0 :: Integer))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                           (coe v0))
                                        erased))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Int_132
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384
                (MAlonzo.Code.Once.CanonicalName.d_bare_12
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("." :: Data.Text.Text) v1)))
                (coe
                   MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230
                   (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_206)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C_Float_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384
                (MAlonzo.Code.Once.CanonicalName.d_bare_12
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("." :: Data.Text.Text) v1)))
                (coe
                   MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230
                   (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_208)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C_Str_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384
                (MAlonzo.Code.Once.CanonicalName.d_bare_12
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("." :: Data.Text.Text) v1)))
                (coe
                   MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230
                   (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Str_210)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C_Buffer_138
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384
                (MAlonzo.Code.Once.CanonicalName.d_bare_12
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         ("." :: Data.Text.Text) v1)))
                (coe
                   MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230
                   (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Buffer_212)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
                   erased))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.infer-complete-RResolved
d_infer'45'complete'45'RResolved_212 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RResolved_212 v0 v1 v2 ~v3 v4
  = du_infer'45'complete'45'RResolved_212 v0 v1 v2 v4
du_infer'45'complete'45'RResolved_212 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RResolved_212 v0 v1 v2 v3
  = coe du_go_272 (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.TypeCheck.Completeness._.helper
d_helper_232 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helper_232 = erased
-- Once.TypeCheck.Completeness._.helperArr
d_helperArr_250 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helperArr_250 = erased
-- Once.TypeCheck.Completeness._.helperVal
d_helperVal_260 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helperVal_260 = erased
-- Once.TypeCheck.Completeness._.go
d_go_272 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_272 v0 v1 ~v2 ~v3 ~v4 v5 v6 ~v7 = du_go_272 v0 v1 v5 v6
du_go_272 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_272 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Type.C_Unit_118
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384 v1
                (coe
                   MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230
                   (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C_Void_120
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384 v1
                (coe
                   MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230
                   (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Void_204)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C__'42'__122 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384 v1
                (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63''45'complete_152
                      (coe v2) (coe v3))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C__'43'__124 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384 v1
                (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                   (coe
                      MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63''45'complete_152
                      (coe v2) (coe v3))))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v4 v5 v6
        -> case coe v5 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v7 v8
               -> case coe v7 of
                    MAlonzo.Code.Once.Type.C_Zero_6
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384 v1
                              (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63''45'complete_152
                                    (coe v2) (coe v3))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                    (coe v0))
                                 erased))
                    MAlonzo.Code.Once.Type.C_One_8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384 v1
                              (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                 (coe
                                    MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63''45'complete_152
                                    (coe v2) (coe v3))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                    (coe v0))
                                 erased))
                    MAlonzo.Code.Once.Type.C_Many_10
                      -> case coe v3 of
                           MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_238 v12 v13
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                     (coe
                                        MAlonzo.Code.Once.IR.C_SigOp_156 (coe v4) (coe v6)
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.d_ext'45'resolved'45'info_1990
                                           (coe v4) (coe v6) (coe v0) (coe v1) (coe v8)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                              (coe
                                                 MAlonzo.Code.Once.Functor.Decide.d_isBaseType'63''45'complete_90
                                                 (coe v4) (coe v12)))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                              (coe
                                                 MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63''45'complete_152
                                                 (coe v6) (coe v13))))))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe (0 :: Integer))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                           (coe v0))
                                        erased))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_Int_132
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384 v1
                (coe
                   MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230
                   (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_206)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C_Float_134
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384 v1
                (coe
                   MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230
                   (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_208)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C_Str_136
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384 v1
                (coe
                   MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230
                   (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Str_210)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
                   erased))
      MAlonzo.Code.Once.Type.C_Buffer_138
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384 v1
                (coe
                   MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230
                   (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Buffer_212)))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
                   erased))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.infer-complete-RPair
d_infer'45'complete'45'RPair_374 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RPair_374 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                                 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14
  = du_infer'45'complete'45'RPair_374 v0 v1 v2
du_infer'45'complete'45'RPair_374 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RPair_374 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v6 v7 v8 v9 v10
                  -> let v11
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                               (coe v0) (coe v2) in
                     coe
                       (case coe v11 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                            -> case coe v12 of
                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v14 v15 v16 v17 v18
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_pair_76 v7 v15 v8 v16)
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
d_infer'45'complete'45'RUnaryOp'45'neg_432 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RUnaryOp'45'neg_432 v0 v1 ~v2 ~v3 ~v4 ~v5
                                           ~v6
  = du_infer'45'complete'45'RUnaryOp'45'neg_432 v0 v1
du_infer'45'complete'45'RUnaryOp'45'neg_432 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RUnaryOp'45'neg_432 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_negOperandView_350
              (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_nov'45'int_332
           -> case coe v1 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_int_184
                          (MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v4)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
                             erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.TypeCheck.Elaborate.C_nov'45'other_346
           -> let v4
                    = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                        (coe v0) (coe v1) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                     -> case coe v5 of
                          MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                            -> coe
                                 seq (coe v7)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe MAlonzo.Code.Once.Surface.Syntax.C_neg_304 v9)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                       (coe addInt (coe (1 :: Integer)) (coe v10))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                          erased)))
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.infer-complete-RAnnot
d_infer'45'complete'45'RAnnot_502 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RAnnot_502 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_infer'45'complete'45'RAnnot_502 v0 v1 v2
du_infer'45'complete'45'RAnnot_502 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RAnnot_502 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_1476
              (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_324 v6 v7 v8 v9
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.infer-complete-RLet
d_infer'45'complete'45'RLet_560 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RLet_560 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                                ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16
  = du_infer'45'complete'45'RLet_560 v0 v1 v2 v3
du_infer'45'complete'45'RLet_560 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RLet_560 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
              (coe v0) (coe v2) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                  -> let v12
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                               (coe
                                  MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402 (coe v0)
                                  (coe v1) (coe v7))
                               (coe v3) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                            -> case coe v13 of
                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v15 v16 v17 v18 v19
                                   -> case coe v16 of
                                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v21 v22
                                          -> coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.C_let''_178 v8
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
d_infer'45'complete'45'RApp'45'id_632 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RApp'45'id_632 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_infer'45'complete'45'RApp'45'id_632 v0 v1
du_infer'45'complete'45'RApp'45'id_632 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'id_632 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v5 v6 v7 v8 v9
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426 v6 v5
                          (coe MAlonzo.Code.Once.IR.C_id_22) v7)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe addInt (coe (1 :: Integer)) (coe v8))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.infer-complete-RApp-terminal
d_infer'45'complete'45'RApp'45'terminal_670 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RApp'45'terminal_670 v0 v1 ~v2 ~v3 ~v4 ~v5
                                            ~v6 ~v7
  = du_infer'45'complete'45'RApp'45'terminal_670 v0 v1
du_infer'45'complete'45'RApp'45'terminal_670 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'terminal_670 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v5 v6 v7 v8 v9
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426 v6 v5
                          (coe MAlonzo.Code.Once.IR.C_terminal_74) v7)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe addInt (coe (1 :: Integer)) (coe v8))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.infer-complete-RApp-fst
d_infer'45'complete'45'RApp'45'fst_710 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RApp'45'fst_710 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 ~v8
  = du_infer'45'complete'45'RApp'45'fst_710 v0 v1
du_infer'45'complete'45'RApp'45'fst_710 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'fst_710 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v5 v6 v7 v8 v9
                  -> coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426 v6 v5
                             (coe MAlonzo.Code.Once.IR.C_fst_44) v7)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe addInt (coe (1 :: Integer)) (coe v8))
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased)))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.infer-complete-RApp-snd
d_infer'45'complete'45'RApp'45'snd_750 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RApp'45'snd_750 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 ~v8
  = du_infer'45'complete'45'RApp'45'snd_750 v0 v1
du_infer'45'complete'45'RApp'45'snd_750 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'snd_750 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
              (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v5 v6 v7 v8 v9
                  -> coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426 v6 v5
                             (coe MAlonzo.Code.Once.IR.C_snd_50) v7)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe addInt (coe (1 :: Integer)) (coe v8))
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased)))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.infer-complete-RApp-apply
d_infer'45'complete'45'RApp'45'apply_790 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RApp'45'apply_790 v0 v1 v2 ~v3 ~v4 ~v5 ~v6
                                         ~v7 ~v8
  = du_infer'45'complete'45'RApp'45'apply_790 v0 v1 v2
du_infer'45'complete'45'RApp'45'apply_790 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'apply_790 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v6 v7 v8 v9 v10
                  -> case coe v6 of
                       MAlonzo.Code.Once.Type.C__'42'__122 v11 v12
                         -> case coe v11 of
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
                                -> case coe v14 of
                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50 v16 v17
                                       -> coe
                                            seq (coe v16)
                                            (coe
                                               seq (coe v17)
                                               (let v18
                                                      = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
                                                                         MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426
                                                                         v7
                                                                         (coe
                                                                            MAlonzo.Code.Once.Type.C__'42'__122
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
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
                                                                            MAlonzo.Code.Once.IR.C_apply_92)
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
d_infer'45'complete'45'RVar'45'local_856 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_SVar_210 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RVar'45'local_856 v0 v1 ~v2 ~v3 v4 ~v5 ~v6
  = du_infer'45'complete'45'RVar'45'local_856 v0 v1 v4
du_infer'45'complete'45'RVar'45'local_856 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Surface.Context.T_SVar_210 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RVar'45'local_856 v0 v1 v2
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
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.du_svar'8594'expr_526 (coe v2))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
                                erased)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness._.helper
d_helper_916 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_SVar_210 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helper_916 = erased
-- Once.TypeCheck.Completeness.infer-complete-RVar-import
d_infer'45'complete'45'RVar'45'import_930 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RVar'45'import_930 v0 v1 v2 ~v3 ~v4 ~v5 v6
  = du_infer'45'complete'45'RVar'45'import_930 v0 v1 v2 v6
du_infer'45'complete'45'RVar'45'import_930 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RVar'45'import_930 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v4 ->
                 coe
                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                   (coe v1))
              (coe
                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v1)
                 (coe ("unit" :: Data.Text.Text))) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then coe
                       seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                else coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384
                             (MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v1))
                             (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Once.Functor.Decide.d_isConcrete'63''45'complete_152
                                   (coe v2) (coe v3))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
                                erased)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness._.helperLoc
d_helperLoc_990 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helperLoc_990 = erased
-- Once.TypeCheck.Completeness._.helperImp
d_helperImp_996 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helperImp_996 = erased
-- Once.TypeCheck.Completeness._.helperImpVal
d_helperImpVal_1002 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  Maybe MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_helperImpVal_1002 = erased
-- Once.TypeCheck.Completeness.infer-complete-RBinOp-arith-float-il
d_infer'45'complete'45'RBinOp'45'arith'45'float'45'il_1036 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RBinOp'45'arith'45'float'45'il_1036 v0 v1
                                                           ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                                                           ~v12 ~v13 ~v14
  = du_infer'45'complete'45'RBinOp'45'arith'45'float'45'il_1036
      v0 v1 v3 v4
du_infer'45'complete'45'RBinOp'45'arith'45'float'45'il_1036 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RBinOp'45'arith'45'float'45'il_1036 v0 v1
                                                            v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
        -> let v4
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_fadd_238
                                                        v8 v16
                                                        (coe
                                                           MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                                           v9)
                                                        v17)
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_fsub_248
                                                        v8 v16
                                                        (coe
                                                           MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                                           v9)
                                                        v17)
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_fmul_258
                                                        v8 v16
                                                        (coe
                                                           MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                                           v9)
                                                        v17)
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_fdiv_268
                                                        v8 v16
                                                        (coe
                                                           MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                                           v9)
                                                        v17)
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
-- Once.TypeCheck.Completeness.infer-complete-RBinOp-arith-float-ir
d_infer'45'complete'45'RBinOp'45'arith'45'float'45'ir_1222 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RBinOp'45'arith'45'float'45'ir_1222 v0 v1
                                                           ~v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                                                           ~v12 ~v13 ~v14
  = du_infer'45'complete'45'RBinOp'45'arith'45'float'45'ir_1222
      v0 v1 v3 v4
du_infer'45'complete'45'RBinOp'45'arith'45'float'45'ir_1222 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RBinOp'45'arith'45'float'45'ir_1222 v0 v1
                                                            v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
        -> let v4
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_fadd_238
                                                        v8 v16 v9
                                                        (coe
                                                           MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                                           v17))
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_fsub_248
                                                        v8 v16 v9
                                                        (coe
                                                           MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                                           v17))
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_fmul_258
                                                        v8 v16 v9
                                                        (coe
                                                           MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                                           v17))
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_fdiv_268
                                                        v8 v16 v9
                                                        (coe
                                                           MAlonzo.Code.Once.Surface.Syntax.C_i2f_276
                                                           v17))
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
-- Once.TypeCheck.Completeness.infer-complete-RBinOp-arith-float
d_infer'45'complete'45'RBinOp'45'arith'45'float_1408 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RBinOp'45'arith'45'float_1408 v0 v1 ~v2 v3
                                                     v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14
  = du_infer'45'complete'45'RBinOp'45'arith'45'float_1408 v0 v1 v3 v4
du_infer'45'complete'45'RBinOp'45'arith'45'float_1408 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RBinOp'45'arith'45'float_1408 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
        -> let v4
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_fadd_238
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_fsub_248
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_fmul_258
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_fdiv_268
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
-- Once.TypeCheck.Completeness.infer-complete-RBinOp-arith
d_infer'45'complete'45'RBinOp'45'arith_1594 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RBinOp'45'arith_1594 v0 v1 ~v2 v3 v4 ~v5 ~v6
                                            ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14
  = du_infer'45'complete'45'RBinOp'45'arith_1594 v0 v1 v3 v4
du_infer'45'complete'45'RBinOp'45'arith_1594 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RBinOp'45'arith_1594 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
        -> let v4
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_add_208
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_sub_218
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_mul_228
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_div_286
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_mod''_296
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
d_infer'45'complete'45'RBinOp'45'cmp_1818 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RBinOp'45'cmp_1818 v0 v1 ~v2 v3 v4 ~v5 ~v6
                                          ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14
  = du_infer'45'complete'45'RBinOp'45'cmp_1818 v0 v1 v3 v4
du_infer'45'complete'45'RBinOp'45'cmp_1818 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RBinOp'45'cmp_1818 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_OpLt_18
        -> let v4
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_lt_314 v8
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_le_324 v8
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_gt_334 v8
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_ge_344 v8
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_eq_354 v8
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                                         (coe v0) (coe v3) in
                               coe
                                 (case coe v12 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                      -> case coe v13 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v15 v16 v17 v18 v19
                                             -> coe
                                                  seq (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_ne_364 v8
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
d_decideLeq'45'just_2054 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_decideLeq'45'just_2054 v0 v1 ~v2
  = du_decideLeq'45'just_2054 v0 v1
du_decideLeq'45'just_2054 ::
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_decideLeq'45'just_2054 v0 v1
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
-- Once.TypeCheck.Completeness.check-complete-RLam
d_check'45'complete'45'RLam_2084 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_check'45'complete'45'RLam_2084 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 ~v9
                                 ~v10 ~v11 ~v12
  = du_check'45'complete'45'RLam_2084 v0 v1 v2 v3 v4 v5 v6
du_check'45'complete'45'RLam_2084 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_check'45'complete'45'RLam_2084 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_1476
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402 (coe v0)
                 (coe v1) (coe v3))
              (coe v2) (coe v6) in
    coe
      (case coe v7 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
           -> case coe v8 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_324 v10 v11 v12 v13
                  -> coe
                       seq (coe v10)
                       (let v14
                              = MAlonzo.Code.Once.TypeCheck.Elaborate.d_decideLeq_1178
                                  (coe v5) (coe v4) in
                        coe
                          (let v15 = coe du_decideLeq'45'just_2054 (coe v5) (coe v4) in
                           coe
                             (coe
                                seq (coe v14)
                                (coe
                                   seq (coe v15)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                      (coe MAlonzo.Code.Once.Surface.Syntax.C_lam_32 v5 v11)
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe addInt (coe (1 :: Integer)) (coe v12))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                            erased)))))))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.check-complete-RLam-eff
d_check'45'complete'45'RLam'45'eff_2174 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_check'45'complete'45'RLam'45'eff_2174 v0 v1 v2 v3 v4 v5 ~v6 ~v7
                                        ~v8 ~v9 ~v10 ~v11
  = du_check'45'complete'45'RLam'45'eff_2174 v0 v1 v2 v3 v4 v5
du_check'45'complete'45'RLam'45'eff_2174 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_check'45'complete'45'RLam'45'eff_2174 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_1476
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402 (coe v0)
                 (coe v1) (coe v3))
              (coe v2) (coe v5) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
           -> case coe v7 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_324 v9 v10 v11 v12
                  -> coe
                       seq (coe v9)
                       (let v13
                              = MAlonzo.Code.Once.TypeCheck.Elaborate.d_decideLeq_1178
                                  (coe v4) (coe MAlonzo.Code.Once.Type.C_Many_10) in
                        coe
                          (let v14
                                 = coe
                                     du_decideLeq'45'just_2054 (coe v4)
                                     (coe MAlonzo.Code.Once.Type.C_Many_10) in
                           coe
                             (coe
                                seq (coe v13)
                                (coe
                                   seq (coe v14)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                      (coe
                                         MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
                                         (coe MAlonzo.Code.Once.Surface.Syntax.C_lam_32 v4 v10))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe addInt (coe (1 :: Integer)) (coe v11))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                            erased)))))))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.infer-complete-RDestruct
d_infer'45'complete'45'RDestruct_2284 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RDestruct_2284 v0 v1 v2 v3 v4 v5 ~v6 ~v7 ~v8
                                      ~v9 ~v10 ~v11 v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21
                                      ~v22 ~v23 ~v24 ~v25
  = du_infer'45'complete'45'RDestruct_2284 v0 v1 v2 v3 v4 v5 v12
du_infer'45'complete'45'RDestruct_2284 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RDestruct_2284 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
              (coe v0) (coe v1) in
    coe
      (case coe v7 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
           -> case coe v8 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v10 v11 v12 v13 v14
                  -> case coe v10 of
                       MAlonzo.Code.Once.Type.C__'43'__124 v15 v16
                         -> let v17
                                  = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402
                                         (coe v0) (coe v2) (coe v15))
                                      (coe v3) in
                            coe
                              (case coe v17 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                   -> case coe v18 of
                                        MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v20 v21 v22 v23 v24
                                          -> case coe v21 of
                                               MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v26 v27
                                                 -> let v28
                                                          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
                                                              (coe
                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402
                                                                 (coe v0) (coe v4) (coe v16))
                                                              (coe v5) in
                                                    coe
                                                      (case coe v28 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v29 v30
                                                           -> case coe v29 of
                                                                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v31 v32 v33 v34 v35
                                                                  -> case coe v32 of
                                                                       MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v37 v38
                                                                         -> let v39
                                                                                  = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
                                                                                                     MAlonzo.Code.Once.Surface.Syntax.C_case''_146
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
d_infer'45'complete'45'RApp'45'generic_2482 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RApp'45'generic_2482 v0 v1 v2 v3 ~v4 v5 ~v6
                                            ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16
  = du_infer'45'complete'45'RApp'45'generic_2482 v0 v1 v2 v3 v5
du_infer'45'complete'45'RApp'45'generic_2482 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'generic_2482 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
              (coe v0) (coe v1) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> case coe v6 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v8 v9 v10 v11 v12
                  -> let v13
                           = coe
                               MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_1476
                               (coe v0) (coe v2) (coe v3) in
                     coe
                       (case coe v13 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                            -> case coe v14 of
                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_324 v16 v17 v18 v19
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_app_48 v9 v16 v3 v4
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
d_viewBridge_2494 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_AppHeadView_1062 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_viewBridge_2494 = erased
-- Once.TypeCheck.Completeness.otherBridge
d_otherBridge_2506 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Classify.T_PolyBuiltinApp_1032 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_otherBridge_2506 = erased
-- Once.TypeCheck.Completeness.infer-complete-RApp-eff
d_infer'45'complete'45'RApp'45'eff_2610 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete'45'RApp'45'eff_2610 v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7
                                        ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15
  = du_infer'45'complete'45'RApp'45'eff_2610 v0 v1 v2 v3
du_infer'45'complete'45'RApp'45'eff_2610 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete'45'RApp'45'eff_2610 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460
              (coe v0) (coe v1) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                  -> let v12
                           = coe
                               MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_1476
                               (coe v0) (coe v2) (coe v3) in
                     coe
                       (case coe v12 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                            -> case coe v13 of
                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_324 v15 v16 v17 v18
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_effApp_62 v8 v15 v3 v9
                                           v16)
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
d_checkElab'45'fallback'45'RVar_2696 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'fallback'45'RVar_2696 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_checkElab'45'fallback'45'RVar_2696 v0 v1 v2
du_checkElab'45'fallback'45'RVar_2696 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'fallback'45'RVar_2696 v0 v1 v2
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
                               (coe MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'id_1316) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'id_1316
                            -> let v7
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1762
                                         (coe v0) (coe ("id" :: Data.Text.Text))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                               (coe v0))
                                            (coe ("id" :: Data.Text.Text))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_named_356
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                               (coe v0)))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                               (coe v0))
                                            (coe ("id" :: Data.Text.Text))) in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                      -> case coe v8 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v10 v11 v12 v13 v14
                                             -> let v15
                                                      = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'fst_1318
                            -> let v7
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1762
                                         (coe v0) (coe ("fst" :: Data.Text.Text))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                               (coe v0))
                                            (coe ("fst" :: Data.Text.Text))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_named_356
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                               (coe v0)))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                               (coe v0))
                                            (coe ("fst" :: Data.Text.Text))) in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                      -> case coe v8 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v10 v11 v12 v13 v14
                                             -> let v15
                                                      = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'snd_1320
                            -> let v7
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1762
                                         (coe v0) (coe ("snd" :: Data.Text.Text))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                               (coe v0))
                                            (coe ("snd" :: Data.Text.Text))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_named_356
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                               (coe v0)))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                               (coe v0))
                                            (coe ("snd" :: Data.Text.Text))) in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                      -> case coe v8 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v10 v11 v12 v13 v14
                                             -> let v15
                                                      = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'terminal_1322
                            -> let v7
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1762
                                         (coe v0) (coe ("terminal" :: Data.Text.Text))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                               (coe v0))
                                            (coe ("terminal" :: Data.Text.Text))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_named_356
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                               (coe v0)))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                               (coe v0))
                                            (coe ("terminal" :: Data.Text.Text))) in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                      -> case coe v8 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v10 v11 v12 v13 v14
                                             -> let v15
                                                      = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'initial_1324
                            -> let v7
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1762
                                         (coe v0) (coe ("initial" :: Data.Text.Text))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                               (coe v0))
                                            (coe ("initial" :: Data.Text.Text))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_named_356
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                               (coe v0)))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                               (coe v0))
                                            (coe ("initial" :: Data.Text.Text))) in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                      -> case coe v8 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v10 v11 v12 v13 v14
                                             -> let v15
                                                      = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inl_1326
                            -> let v7
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1762
                                         (coe v0) (coe ("inl" :: Data.Text.Text))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                               (coe v0))
                                            (coe ("inl" :: Data.Text.Text))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_named_356
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                               (coe v0)))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                               (coe v0))
                                            (coe ("inl" :: Data.Text.Text))) in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                      -> case coe v8 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v10 v11 v12 v13 v14
                                             -> let v15
                                                      = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inr_1328
                            -> let v7
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1762
                                         (coe v0) (coe ("inr" :: Data.Text.Text))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                               (coe v0))
                                            (coe ("inr" :: Data.Text.Text))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_named_356
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                               (coe v0)))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                               (coe v0))
                                            (coe ("inr" :: Data.Text.Text))) in
                               coe
                                 (case coe v7 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                      -> case coe v8 of
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v10 v11 v12 v13 v14
                                             -> let v15
                                                      = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'other_1332
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
                                                                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Unit_118)
                                                                (coe
                                                                   MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                                   (coe
                                                                      MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                                      (coe v0)))
                                                                (coe
                                                                   MAlonzo.Code.Once.Surface.Syntax.C_unit_152)
                                                                (coe (0 :: Integer))
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                   (coe v0)))
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_48)) in
                                                coe
                                                  (case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                       -> case coe v12 of
                                                            MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v14 v15 v16 v17 v18
                                                              -> let v19
                                                                       = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
                                                              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1762
                                                              (coe v0) (coe v1)
                                                              (coe
                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal_572
                                                                 (coe v0) (coe v1))
                                                              (coe
                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                                                 (coe
                                                                    MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                                                    (coe v0))
                                                                 (coe v1))) in
                                                 coe
                                                   (case coe v11 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                        -> case coe v12 of
                                                             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v14 v15 v16 v17 v18
                                                               -> let v19
                                                                        = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
                                                       MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'fst_1318)
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
                                                                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'snd_1320)
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
                                                                                               MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'terminal_1322)
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
                                                                                                                   MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'initial_1324)
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
                                                                                                                                       MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inl_1326)
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
                                                                                                                                                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inr_1328)
                                                                                                                                                 else coe
                                                                                                                                                        seq
                                                                                                                                                        (coe
                                                                                                                                                           v23)
                                                                                                                                                        (coe
                                                                                                                                                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'other_1332)
                                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                      _ -> MAlonzo.RTE.mazUnreachableError)) in
                      coe
                        (case coe v6 of
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'id_1316
                             -> let v7
                                      = coe
                                          MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1762
                                          (coe v0) (coe ("id" :: Data.Text.Text))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                (coe v0))
                                             (coe ("id" :: Data.Text.Text))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_named_356
                                                (coe v0))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                (coe v0)))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                                (coe v0))
                                             (coe ("id" :: Data.Text.Text))) in
                                coe
                                  (case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                       -> case coe v8 of
                                            MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v10 v11 v12 v13 v14
                                              -> let v15
                                                       = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'fst_1318
                             -> let v7
                                      = coe
                                          MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1762
                                          (coe v0) (coe ("fst" :: Data.Text.Text))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                (coe v0))
                                             (coe ("fst" :: Data.Text.Text))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_named_356
                                                (coe v0))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                (coe v0)))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                                (coe v0))
                                             (coe ("fst" :: Data.Text.Text))) in
                                coe
                                  (case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                       -> case coe v8 of
                                            MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v10 v11 v12 v13 v14
                                              -> let v15
                                                       = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'snd_1320
                             -> let v7
                                      = coe
                                          MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1762
                                          (coe v0) (coe ("snd" :: Data.Text.Text))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                (coe v0))
                                             (coe ("snd" :: Data.Text.Text))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_named_356
                                                (coe v0))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                (coe v0)))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                                (coe v0))
                                             (coe ("snd" :: Data.Text.Text))) in
                                coe
                                  (case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                       -> case coe v8 of
                                            MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v10 v11 v12 v13 v14
                                              -> let v15
                                                       = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'terminal_1322
                             -> let v7
                                      = coe
                                          MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1762
                                          (coe v0) (coe ("terminal" :: Data.Text.Text))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                (coe v0))
                                             (coe ("terminal" :: Data.Text.Text))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_named_356
                                                (coe v0))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                (coe v0)))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                                (coe v0))
                                             (coe ("terminal" :: Data.Text.Text))) in
                                coe
                                  (case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                       -> case coe v8 of
                                            MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v10 v11 v12 v13 v14
                                              -> let v15
                                                       = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'initial_1324
                             -> let v7
                                      = coe
                                          MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1762
                                          (coe v0) (coe ("initial" :: Data.Text.Text))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                (coe v0))
                                             (coe ("initial" :: Data.Text.Text))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_named_356
                                                (coe v0))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                (coe v0)))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                                (coe v0))
                                             (coe ("initial" :: Data.Text.Text))) in
                                coe
                                  (case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                       -> case coe v8 of
                                            MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v10 v11 v12 v13 v14
                                              -> let v15
                                                       = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inl_1326
                             -> let v7
                                      = coe
                                          MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1762
                                          (coe v0) (coe ("inl" :: Data.Text.Text))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                (coe v0))
                                             (coe ("inl" :: Data.Text.Text))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_named_356
                                                (coe v0))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                (coe v0)))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                                (coe v0))
                                             (coe ("inl" :: Data.Text.Text))) in
                                coe
                                  (case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                       -> case coe v8 of
                                            MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v10 v11 v12 v13 v14
                                              -> let v15
                                                       = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inr_1328
                             -> let v7
                                      = coe
                                          MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1762
                                          (coe v0) (coe ("inr" :: Data.Text.Text))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                (coe v0))
                                             (coe ("inr" :: Data.Text.Text))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_named_356
                                                (coe v0))
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                (coe v0)))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                                (coe v0))
                                             (coe ("inr" :: Data.Text.Text))) in
                                coe
                                  (case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                       -> case coe v8 of
                                            MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v10 v11 v12 v13 v14
                                              -> let v15
                                                       = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'other_1332
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
                                                                 MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300
                                                                 (coe
                                                                    MAlonzo.Code.Once.Type.C_Unit_118)
                                                                 (coe
                                                                    MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                                    (coe
                                                                       MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                                       (coe v0)))
                                                                 (coe
                                                                    MAlonzo.Code.Once.Surface.Syntax.C_unit_152)
                                                                 (coe (0 :: Integer))
                                                                 (coe
                                                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                    (coe v0)))
                                                              (coe
                                                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_48)) in
                                                 coe
                                                   (case coe v11 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                        -> case coe v12 of
                                                             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v14 v15 v16 v17 v18
                                                               -> let v19
                                                                        = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
                                                               MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1762
                                                               (coe v0) (coe v1)
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal_572
                                                                  (coe v0) (coe v1))
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                                                  (coe
                                                                     MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                                                     (coe v0))
                                                                  (coe v1))) in
                                                  coe
                                                    (case coe v11 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                         -> case coe v12 of
                                                              MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v14 v15 v16 v17 v18
                                                                -> let v19
                                                                         = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
d_completeness'45'gap'45'inl'45'app'45'check'45'eq_3068 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_completeness'45'gap'45'inl'45'app'45'check'45'eq_3068 v0 v1 v2
                                                        ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_completeness'45'gap'45'inl'45'app'45'check'45'eq_3068 v0 v1 v2
du_completeness'45'gap'45'inl'45'app'45'check'45'eq_3068 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_completeness'45'gap'45'inl'45'app'45'check'45'eq_3068 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_1476
              (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_324 v6 v7 v8 v9
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426 v6 v2
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
d_completeness'45'gap'45'inr'45'app'45'check'45'eq_3116 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_completeness'45'gap'45'inr'45'app'45'check'45'eq_3116 v0 v1 ~v2
                                                        v3 ~v4 ~v5 ~v6 ~v7 ~v8
  = du_completeness'45'gap'45'inr'45'app'45'check'45'eq_3116 v0 v1 v3
du_completeness'45'gap'45'inr'45'app'45'check'45'eq_3116 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_completeness'45'gap'45'inr'45'app'45'check'45'eq_3116 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_1476
              (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_324 v6 v7 v8 v9
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426 v6 v2
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
d_completeness'45'gap'45'initial'45'app'45'check'45'eq_3162 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_completeness'45'gap'45'initial'45'app'45'check'45'eq_3162 v0 v1
                                                            ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_completeness'45'gap'45'initial'45'app'45'check'45'eq_3162
      v0 v1
du_completeness'45'gap'45'initial'45'app'45'check'45'eq_3162 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_completeness'45'gap'45'initial'45'app'45'check'45'eq_3162 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_1476
              (coe v0) (coe v1) (coe MAlonzo.Code.Once.Type.C_Void_120) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
           -> case coe v3 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_324 v5 v6 v7 v8
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426 v5
                          (coe MAlonzo.Code.Once.Type.C_Void_120)
                          (coe MAlonzo.Code.Once.IR.C_initial_78) v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe addInt (coe (1 :: Integer)) (coe v7))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8) erased))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.embedOrSubsume-lifts
d_embedOrSubsume'45'lifts_3208 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_embedOrSubsume'45'lifts_3208 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_embedOrSubsume'45'lifts_3208 v2 v3 v4
du_embedOrSubsume'45'lifts_3208 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_embedOrSubsume'45'lifts_3208 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v5 v6 v7 v8 v9
               -> let v10
                        = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                            (coe
                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v0)
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
                                 (coe
                                    seq (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                    (let v13
                                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                               (coe v0) (coe v0) in
                                     coe
                                       (case coe v13 of
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                            -> if coe v14
                                                 then coe
                                                        seq (coe v15)
                                                        (let v16
                                                               = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                                   (coe v1) (coe v1) in
                                                         coe
                                                           (case coe v16 of
                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                -> if coe v17
                                                                     then case coe v18 of
                                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v19
                                                                              -> coe
                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
                                                                                      v7)
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                      (coe v8)
                                                                                      (coe
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                         (coe v9)
                                                                                         erased))
                                                                            _ -> coe
                                                                                   seq (coe v17)
                                                                                   (coe
                                                                                      seq (coe v18)
                                                                                      (coe
                                                                                         MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
                                                                     else (case coe v18 of
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                               -> coe
                                                                                    MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                             _ -> coe
                                                                                    seq (coe v17)
                                                                                    (coe
                                                                                       seq (coe v18)
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)))
                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                 else coe
                                                        seq (coe v15)
                                                        (coe
                                                           MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                          _ -> MAlonzo.RTE.mazUnreachableError))))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.completeness-gap-arg-driven-app-check
d_completeness'45'gap'45'arg'45'driven'45'app'45'check_3430
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.Completeness.completeness-gap-arg-driven-app-check"
-- Once.TypeCheck.Completeness.completeness-gap-arg-driven-app-check-eff
d_completeness'45'gap'45'arg'45'driven'45'app'45'check'45'eff_3454
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.Completeness.completeness-gap-arg-driven-app-check-eff"
-- Once.TypeCheck.Completeness.go-canonical
d_go'45'canonical_3472 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go'45'canonical_3472 = erased
-- Once.TypeCheck.Completeness.composeGo-success
d_composeGo'45'success_3514 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_composeGo'45'success_3514 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10 ~v11 ~v12 v13 v14 v15 ~v16 ~v17 ~v18 ~v19
  = du_composeGo'45'success_3514 v13 v14 v15
du_composeGo'45'success_3514 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_composeGo'45'success_3514 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v0) (coe v2)))
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased)
-- Once.TypeCheck.Completeness.caseGo-success
d_caseGo'45'success_3568 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_caseGo'45'success_3568 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10 ~v11 ~v12 v13 v14 v15 ~v16 ~v17 ~v18
  = du_caseGo'45'success_3568 v13 v14 v15
du_caseGo'45'success_3568 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_caseGo'45'success_3568 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v0) (coe v2)))
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased)
-- Once.TypeCheck.Completeness.check-completeV
d_check'45'completeV_3672 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_check'45'completeV_3672 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_1476
              (coe v0) (coe v1) (coe v2) in
    coe
      (let v6
             = d_check'45'complete_3824
                 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) in
       coe
         (case coe v5 of
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
              -> case coe v6 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                     -> case coe v10 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                            -> case coe v12 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v8) erased)))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.TypeCheck.Completeness.subsume-completeV
d_subsume'45'completeV_3692 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_subsume'45'completeV_3692 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_1476
              (coe v0) (coe v1)
              (coe
                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v2)
                 (coe
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                    (coe MAlonzo.Code.Once.Type.C_eff_36))
                 (coe v3)) in
    coe
      (let v7
             = d_subsume'45'complete_3842
                 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) in
       coe
         (case coe v6 of
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
              -> case coe v7 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                     -> case coe v11 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                            -> case coe v13 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v14)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v9) erased)))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.TypeCheck.Completeness.iFromInfer
d_iFromInfer_3708 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_iFromInfer_3708 v0 v1 v2 ~v3 v4 = du_iFromInfer_3708 v0 v1 v2 v4
du_iFromInfer_3708 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_iFromInfer_3708 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_22
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v6
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.d_checkElab'45'fallback'45'RInt_16
                    (coe v0) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'float_34
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v9 v10 v11 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RFloat_52
                    (coe v0) (coe v9) (coe v10) (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'str_40
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_58 v6
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.d_checkElab'45'fallback'45'RStringLit_100
                    (coe v0) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_44
        -> coe
             MAlonzo.Code.Once.TypeCheck.ElaborateProofs.d_checkElab'45'fallback'45'RUnit_128
             (coe v0)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_48
        -> coe
             MAlonzo.Code.Once.TypeCheck.ElaborateProofs.d_checkElab'45'fallback'45'RVar'45'unit_1204
             (coe v0)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_60 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v11
               -> coe
                    du_checkElab'45'fallback'45'RVar_2696 (coe v0) (coe v11) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_70 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RQualified_164
                    (coe v0) (coe v10) (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_78 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v9
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RResolved_322
                    (coe v0) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_86 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v11
               -> coe
                    du_checkElab'45'fallback'45'RVar_2696 (coe v0) (coe v11) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_102 v7 v8 v9 v10 v16 v18
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v19
               -> coe
                    du_checkElab'45'fallback'45'RVar_2696 (coe v0) (coe v19) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_112 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v9 v10
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RAnnot_466
                    (coe v0) (coe v9) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_128 v9 v10 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v13 v14
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__122 v15 v16
                      -> let v17
                               = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      du_iFromInfer_3708 (coe v0) (coe v13) (coe v15) (coe v11)) in
                         coe
                           (let v18
                                  = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            du_iFromInfer_3708 (coe v0) (coe v13) (coe v15)
                                            (coe v11))) in
                            coe
                              (coe
                                 du_pair'45'lit'45'reduce_3764 (coe v9) (coe v10) (coe v17)
                                 (coe v18)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe du_iFromInfer_3708 (coe v0) (coe v14) (coe v16) (coe v12)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          du_iFromInfer_3708 (coe v0) (coe v14) (coe v16)
                                          (coe v12))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             du_iFromInfer_3708 (coe v0) (coe v14) (coe v16)
                                             (coe v12)))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_136 v7
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v9
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RUnaryOp_996
                    (coe v0) (coe v9) (coe MAlonzo.Code.Once.Type.C_Int_132)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_148
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v10
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RUnaryOp_996
                    (coe v0) (coe v10) (coe MAlonzo.Code.Once.Type.C_Float_134)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_168 v8 v10 v11 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v15 v16 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RLet_614
                    (coe v0) (coe v15) (coe v16) (coe v17)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_198 v10 v11 v13 v14 v15 v16 v17 v18 v19 v20
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v21 v22 v23 v24 v25
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RDestruct_794
                    (coe v0) (coe v21) (coe v22) (coe v23) (coe v24) (coe v25)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_212 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RBinOp_5360
                    (coe v0) (coe v13) (coe v14) (coe v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_226 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RBinOp_5360
                    (coe v0) (coe v13) (coe v14) (coe v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_240 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RBinOp_5360
                    (coe v0) (coe v13) (coe v14) (coe v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_254 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RBinOp_5360
                    (coe v0) (coe v13) (coe v14) (coe v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_268 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RBinOp_5360
                    (coe v0) (coe v13) (coe v14) (coe v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_278 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'id_4034
                    (coe v0) (coe v10) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_290 v7 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'fst_4104
                    (coe v0) (coe v11) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_302 v6 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'snd_4174
                    (coe v0) (coe v11) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_312 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'terminal_5286
                    (coe v0) (coe v10) (coe MAlonzo.Code.Once.Type.C_Unit_118)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_324 v6 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'apply_2288
                    (coe v0) (coe v11) (coe v6) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_342 v7 v9 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'generic_4260
                    (coe v0) (coe v15) (coe v16) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_358 v7 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v16 v17 v18
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'generic_4260
                           (coe v0) (coe v14) (coe v15)
                           (coe
                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                              (coe MAlonzo.Code.Once.Type.C_Unit_118)
                              (coe
                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                 (coe MAlonzo.Code.Once.Type.C_eff_36))
                              (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.check-completeV-from-infer
d_check'45'completeV'45'from'45'infer_3726 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_check'45'completeV'45'from'45'infer_3726 v0 v1 v2 ~v3 v4
  = du_check'45'completeV'45'from'45'infer_3726 v0 v1 v2 v4
du_check'45'completeV'45'from'45'infer_3726 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_check'45'completeV'45'from'45'infer_3726 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_1476
              (coe v0) (coe v1) (coe v2) in
    coe
      (let v5
             = coe du_iFromInfer_3708 (coe v0) (coe v1) (coe v2) (coe v3) in
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
d_pair'45'lit'45'reduce_3764 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pair'45'lit'45'reduce_3764 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 ~v9
                             ~v10 v11 v12 v13 ~v14 ~v15 ~v16
  = du_pair'45'lit'45'reduce_3764 v5 v6 v7 v8 v11 v12 v13
du_pair'45'lit'45'reduce_3764 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pair'45'lit'45'reduce_3764 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_pair_76 v0 v1 v2 v4)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v3) (coe v5))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) erased))
-- Once.TypeCheck.Completeness.iFromInferEff
d_iFromInferEff_3782 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_iFromInferEff_3782 v0 v1 v2 v3 ~v4 v5
  = du_iFromInferEff_3782 v0 v1 v2 v3 v5
du_iFromInferEff_3782 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_iFromInferEff_3782 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_60 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'eff_4820
                    (coe v0) (coe v12) (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_70 v10
        -> coe
             du_embedOrSubsume'45'lifts_3208 (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460 (coe v0)
                (coe v1))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_78 v9
        -> coe
             du_embedOrSubsume'45'lifts_3208 (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460 (coe v0)
                (coe v1))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_86 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'eff_4820
                    (coe v0) (coe v12) (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_102 v8 v9 v10 v11 v17 v19
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v20
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'eff_4820
                    (coe v0) (coe v20) (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_112 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v10 v11
               -> coe
                    du_embedOrSubsume'45'lifts_3208 (coe v2) (coe v3)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460 (coe v0)
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 (coe v10)
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v2)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe v3))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_168 v9 v11 v12 v13 v14 v15
        -> coe
             du_embedOrSubsume'45'lifts_3208 (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460 (coe v0)
                (coe v1))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_198 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21
        -> coe
             du_embedOrSubsume'45'lifts_3208 (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_1460 (coe v0)
                (coe v1))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_278 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'id'45'eff_4490
                    (coe v0) (coe v11) (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_290 v8 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'fst'45'eff_4600
                    (coe v0) (coe v12) (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_302 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'snd'45'eff_4710
                    (coe v0) (coe v12) (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_324 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'apply'45'eff_4972
                    (coe v0) (coe v12) (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_342 v8 v10 v11 v12 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'generic'45'eff_4348
                    (coe v0) (coe v16) (coe v17) (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.infer-complete
d_infer'45'complete_3798 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete_3798 v0 v1 v2 ~v3 v4
  = du_infer'45'complete_3798 v0 v1 v2 v4
du_infer'45'complete_3798 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete_3798 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_22
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v6
               -> coe d_infer'45'complete'45'RInt_16 (coe v0) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'float_34
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v9 v10 v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Surface.Syntax.C_float_198
                       (MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28
                          (coe v9) (coe v10) (coe v11)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
                          erased))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'str_40
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_58 v6
               -> coe d_infer'45'complete'45'RStringLit_30 (coe v0) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_44
        -> coe d_infer'45'complete'45'RUnit_42 (coe v0)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_48
        -> coe d_infer'45'complete'45'RVar'45'unit_52 (coe v0)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_60 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v11
               -> coe
                    du_infer'45'complete'45'RVar'45'local_856 (coe v0) (coe v11)
                    (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_70 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v10 v11
               -> coe
                    du_infer'45'complete'45'RQualified_68 (coe v0) (coe v10) (coe v11)
                    (coe v2) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_78 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v9
               -> coe
                    du_infer'45'complete'45'RResolved_212 (coe v0) (coe v9) (coe v2)
                    (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_86 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v11
               -> coe
                    du_infer'45'complete'45'RVar'45'import_930 (coe v0) (coe v11)
                    (coe v2) (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_102 v7 v8 v9 v10 v16 v18
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v19
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'poly'45'infer_3992
                    (coe v0) (coe v19)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_112 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v9 v10
               -> coe
                    du_infer'45'complete'45'RAnnot_502 (coe v0) (coe v9) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_128 v9 v10 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v13 v14
               -> coe
                    du_infer'45'complete'45'RPair_374 (coe v0) (coe v13) (coe v14)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_136 v7
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v9
               -> coe
                    du_infer'45'complete'45'RUnaryOp'45'neg_432 (coe v0) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_148
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v10
               -> case coe v10 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v11 v12 v13 v14
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_float_198
                              (MAlonzo.Code.Once.Float.Decimal.d_negate_22
                                 (coe
                                    MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28 (coe v11)
                                    (coe v12) (coe v13))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (1 :: Integer))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                    (coe v0))
                                 erased))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_168 v8 v10 v11 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v15 v16 v17
               -> coe
                    du_infer'45'complete'45'RLet_560 (coe v0) (coe v15) (coe v16)
                    (coe v17)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_198 v10 v11 v13 v14 v15 v16 v17 v18 v19 v20
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v21 v22 v23 v24 v25
               -> coe
                    du_infer'45'complete'45'RDestruct_2284 (coe v0) (coe v21) (coe v22)
                    (coe v23) (coe v24) (coe v25) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_212 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v13 v14 v15
               -> coe
                    du_infer'45'complete'45'RBinOp'45'arith_1594 (coe v0) (coe v13)
                    (coe v14) (coe v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_226 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v13 v14 v15
               -> coe
                    du_infer'45'complete'45'RBinOp'45'arith'45'float_1408 (coe v0)
                    (coe v13) (coe v14) (coe v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_240 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v13 v14 v15
               -> coe
                    du_infer'45'complete'45'RBinOp'45'arith'45'float'45'il_1036
                    (coe v0) (coe v13) (coe v14) (coe v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_254 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v13 v14 v15
               -> coe
                    du_infer'45'complete'45'RBinOp'45'arith'45'float'45'ir_1222
                    (coe v0) (coe v13) (coe v14) (coe v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_268 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v13 v14 v15
               -> coe
                    du_infer'45'complete'45'RBinOp'45'cmp_1818 (coe v0) (coe v13)
                    (coe v14) (coe v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_278 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> coe du_infer'45'complete'45'RApp'45'id_632 (coe v0) (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_290 v7 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe du_infer'45'complete'45'RApp'45'fst_710 (coe v0) (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_302 v6 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe du_infer'45'complete'45'RApp'45'snd_750 (coe v0) (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_312 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> coe
                    du_infer'45'complete'45'RApp'45'terminal_670 (coe v0) (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_324 v6 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    du_infer'45'complete'45'RApp'45'apply_790 (coe v0) (coe v11)
                    (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_342 v7 v9 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> coe
                    du_infer'45'complete'45'RApp'45'generic_2482 (coe v0) (coe v15)
                    (coe v16) (coe v7) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_358 v7 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> coe
                    du_infer'45'complete'45'RApp'45'eff_2610 (coe v0) (coe v14)
                    (coe v15) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.nothing≢just
d_nothing'8802'just_3808 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  () -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_nothing'8802'just_3808 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_nothing'8802'just_3808
du_nothing'8802'just_3808 :: AgdaAny
du_nothing'8802'just_3808 = MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.check-complete
d_check'45'complete_3824 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_check'45'complete_3824 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'check_366
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v10 v11 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'id_1438
                    (coe v0) (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'check_376
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v11 v12 v13
               -> case coe v11 of
                    MAlonzo.Code.Once.Type.C__'42'__122 v14 v15
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'fst_1554
                           (coe v0) (coe v14)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'check_386
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v11 v12 v13
               -> case coe v11 of
                    MAlonzo.Code.Once.Type.C__'42'__122 v14 v15
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'snd_1658
                           (coe v0) (coe v15)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'morph'45'check_394
        -> coe
             MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'terminal_1760
             (coe v0)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'morph'45'check_402
        -> coe
             MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'initial_1894
             (coe v0)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'morph'45'check_412
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v11 v12 v13
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'inl_1962
                    (coe v0) (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'morph'45'check_422
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v11 v12 v13
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'inr_2066
                    (coe v0) (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check_442 v9 v12 v13 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v19 v20
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v21 v22 v23
                             -> case coe v22 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v24 v25
                                    -> case coe v25 of
                                         MAlonzo.Code.Once.Type.C_pure_34
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Syntax.C_comp''_444 v12
                                                   v13 v9
                                                   (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                      (coe
                                                         d_check'45'completeV_3672 (coe v0)
                                                         (coe v20)
                                                         (coe
                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                            (coe v9)
                                                            (coe
                                                               MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                               (coe
                                                                  MAlonzo.Code.Once.Type.C_Many_10)
                                                               (coe v25))
                                                            (coe v23))
                                                         (coe v12) (coe v15)))
                                                   (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                      (coe
                                                         d_check'45'completeV_3672 (coe v0)
                                                         (coe v18)
                                                         (coe
                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                            (coe v21)
                                                            (coe
                                                               MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                               (coe
                                                                  MAlonzo.Code.Once.Type.C_Many_10)
                                                               (coe v25))
                                                            (coe v9))
                                                         (coe v13) (coe v16))))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                      (coe
                                                         du_composeGo'45'success_3514
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                               (coe
                                                                  d_check'45'completeV_3672 (coe v0)
                                                                  (coe v20)
                                                                  (coe
                                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                     (coe v9)
                                                                     (coe
                                                                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                        (coe
                                                                           MAlonzo.Code.Once.Type.C_Many_10)
                                                                        (coe v25))
                                                                     (coe v23))
                                                                  (coe v12) (coe v15))))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                  (coe
                                                                     d_check'45'completeV_3672
                                                                     (coe v0) (coe v20)
                                                                     (coe
                                                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                        (coe v9)
                                                                        (coe
                                                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                           (coe
                                                                              MAlonzo.Code.Once.Type.C_Many_10)
                                                                           (coe v25))
                                                                        (coe v23))
                                                                     (coe v12) (coe v15)))))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                               (coe
                                                                  d_check'45'completeV_3672 (coe v0)
                                                                  (coe v18)
                                                                  (coe
                                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                     (coe v21)
                                                                     (coe
                                                                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                        (coe
                                                                           MAlonzo.Code.Once.Type.C_Many_10)
                                                                        (coe v25))
                                                                     (coe v9))
                                                                  (coe v13) (coe v16))))))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                            (coe
                                                               du_composeGo'45'success_3514
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                     (coe
                                                                        d_check'45'completeV_3672
                                                                        (coe v0) (coe v20)
                                                                        (coe
                                                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                           (coe v9)
                                                                           (coe
                                                                              MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Type.C_Many_10)
                                                                              (coe v25))
                                                                           (coe v23))
                                                                        (coe v12) (coe v15))))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                        (coe
                                                                           d_check'45'completeV_3672
                                                                           (coe v0) (coe v20)
                                                                           (coe
                                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                              (coe v9)
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Type.C_Many_10)
                                                                                 (coe v25))
                                                                              (coe v23))
                                                                           (coe v12) (coe v15)))))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                     (coe
                                                                        d_check'45'completeV_3672
                                                                        (coe v0) (coe v18)
                                                                        (coe
                                                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                           (coe v21)
                                                                           (coe
                                                                              MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Type.C_Many_10)
                                                                              (coe v25))
                                                                           (coe v9))
                                                                        (coe v13) (coe v16)))))))
                                                      erased))
                                         MAlonzo.Code.Once.Type.C_eff_36
                                           -> let v26
                                                    = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                        (coe
                                                           d_check'45'complete_3824 (coe v0)
                                                           (coe v20)
                                                           (coe
                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                              (coe v9)
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                 (coe
                                                                    MAlonzo.Code.Once.Type.C_Many_10)
                                                                 (coe v25))
                                                              (coe v23))
                                                           (coe v12) (coe v15)) in
                                              coe
                                                (let v27
                                                       = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                              (coe
                                                                 d_check'45'complete_3824 (coe v0)
                                                                 (coe v20)
                                                                 (coe
                                                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                    (coe v9)
                                                                    (coe
                                                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                       (coe
                                                                          MAlonzo.Code.Once.Type.C_Many_10)
                                                                       (coe v25))
                                                                    (coe v23))
                                                                 (coe v12) (coe v15))) in
                                                 coe
                                                   (let v28
                                                          = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                    (coe
                                                                       d_check'45'complete_3824
                                                                       (coe v0) (coe v20)
                                                                       (coe
                                                                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                          (coe v9)
                                                                          (coe
                                                                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                             (coe
                                                                                MAlonzo.Code.Once.Type.C_Many_10)
                                                                             (coe v25))
                                                                          (coe v23))
                                                                       (coe v12) (coe v15)))) in
                                                    coe
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Once.Surface.Syntax.C_comp''_444
                                                            v12 v13 v9 v26
                                                            (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                               (coe
                                                                  d_check'45'complete_3824 (coe v0)
                                                                  (coe v18)
                                                                  (coe
                                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                     (coe v21)
                                                                     (coe
                                                                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                        (coe
                                                                           MAlonzo.Code.Once.Type.C_Many_10)
                                                                        (coe v25))
                                                                     (coe v9))
                                                                  (coe v13) (coe v16))))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe
                                                               addInt (coe (1 :: Integer))
                                                               (coe
                                                                  MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                  (coe v27)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                        (coe
                                                                           d_check'45'complete_3824
                                                                           (coe v0) (coe v18)
                                                                           (coe
                                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                              (coe v21)
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Type.C_Many_10)
                                                                                 (coe v25))
                                                                              (coe v9))
                                                                           (coe v13) (coe v16))))))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe v28) erased)))))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case'45'copair'45'check_462 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v20 v21 v22
                             -> case coe v20 of
                                  MAlonzo.Code.Once.Type.C__'43'__124 v23 v24
                                    -> case coe v21 of
                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50 v25 v26
                                           -> case coe v26 of
                                                MAlonzo.Code.Once.Type.C_pure_34
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe
                                                          MAlonzo.Code.Once.Surface.Syntax.C_copair''_462
                                                          v12 v13
                                                          (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                             (coe
                                                                d_check'45'completeV_3672 (coe v0)
                                                                (coe v19)
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                   (coe v23)
                                                                   (coe
                                                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                      (coe
                                                                         MAlonzo.Code.Once.Type.C_Many_10)
                                                                      (coe v26))
                                                                   (coe v22))
                                                                (coe v12) (coe v14)))
                                                          (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                             (coe
                                                                d_check'45'completeV_3672 (coe v0)
                                                                (coe v17)
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                   (coe v24)
                                                                   (coe
                                                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                      (coe
                                                                         MAlonzo.Code.Once.Type.C_Many_10)
                                                                      (coe v26))
                                                                   (coe v22))
                                                                (coe v13) (coe v15))))
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                             (coe
                                                                du_caseGo'45'success_3568
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                      (coe
                                                                         d_check'45'completeV_3672
                                                                         (coe v0) (coe v19)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                            (coe v23)
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Type.C_Many_10)
                                                                               (coe v26))
                                                                            (coe v22))
                                                                         (coe v12) (coe v14))))
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                         (coe
                                                                            d_check'45'completeV_3672
                                                                            (coe v0) (coe v19)
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                               (coe v23)
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Type.C_Many_10)
                                                                                  (coe v26))
                                                                               (coe v22))
                                                                            (coe v12) (coe v14)))))
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                      (coe
                                                                         d_check'45'completeV_3672
                                                                         (coe v0) (coe v17)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                            (coe v24)
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Type.C_Many_10)
                                                                               (coe v26))
                                                                            (coe v22))
                                                                         (coe v13) (coe v15))))))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                   (coe
                                                                      du_caseGo'45'success_3568
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                            (coe
                                                                               d_check'45'completeV_3672
                                                                               (coe v0) (coe v19)
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                  (coe v23)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Type.C_Many_10)
                                                                                     (coe v26))
                                                                                  (coe v22))
                                                                               (coe v12)
                                                                               (coe v14))))
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                            (coe
                                                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                               (coe
                                                                                  d_check'45'completeV_3672
                                                                                  (coe v0) (coe v19)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                     (coe v23)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Type.C_Many_10)
                                                                                        (coe v26))
                                                                                     (coe v22))
                                                                                  (coe v12)
                                                                                  (coe v14)))))
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                            (coe
                                                                               d_check'45'completeV_3672
                                                                               (coe v0) (coe v17)
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                  (coe v24)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Type.C_Many_10)
                                                                                     (coe v26))
                                                                                  (coe v22))
                                                                               (coe v13)
                                                                               (coe v15)))))))
                                                             erased))
                                                MAlonzo.Code.Once.Type.C_eff_36
                                                  -> let v27
                                                           = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                               (coe
                                                                  d_check'45'complete_3824 (coe v0)
                                                                  (coe v19)
                                                                  (coe
                                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                     (coe v23)
                                                                     (coe
                                                                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                        (coe
                                                                           MAlonzo.Code.Once.Type.C_Many_10)
                                                                        (coe v26))
                                                                     (coe v22))
                                                                  (coe v12) (coe v14)) in
                                                     coe
                                                       (let v28
                                                              = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                     (coe
                                                                        d_check'45'complete_3824
                                                                        (coe v0) (coe v19)
                                                                        (coe
                                                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                           (coe v23)
                                                                           (coe
                                                                              MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Type.C_Many_10)
                                                                              (coe v26))
                                                                           (coe v22))
                                                                        (coe v12) (coe v14))) in
                                                        coe
                                                          (let v29
                                                                 = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                           (coe
                                                                              d_check'45'complete_3824
                                                                              (coe v0) (coe v19)
                                                                              (coe
                                                                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                 (coe v23)
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.Type.C_Many_10)
                                                                                    (coe v26))
                                                                                 (coe v22))
                                                                              (coe v12)
                                                                              (coe v14)))) in
                                                           coe
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe
                                                                   MAlonzo.Code.Once.Surface.Syntax.C_copair''_462
                                                                   v12 v13 v27
                                                                   (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                      (coe
                                                                         d_check'45'complete_3824
                                                                         (coe v0) (coe v17)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                            (coe v24)
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Type.C_Many_10)
                                                                               (coe v26))
                                                                            (coe v22))
                                                                         (coe v13) (coe v15))))
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe
                                                                      addInt (coe (1 :: Integer))
                                                                      (coe
                                                                         MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                         (coe v28)
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                            (coe
                                                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                                               (coe
                                                                                  d_check'45'complete_3824
                                                                                  (coe v0) (coe v17)
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                     (coe v24)
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Type.C_Many_10)
                                                                                        (coe v26))
                                                                                     (coe v22))
                                                                                  (coe v13)
                                                                                  (coe v15))))))
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe v29) erased)))))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'morph'45'check_480 v11 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v19 v20 v21
                             -> case coe v21 of
                                  MAlonzo.Code.Once.Type.C__'42'__122 v22 v23
                                    -> let v24
                                             = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                 (coe
                                                    d_check'45'complete_3824 (coe v0) (coe v18)
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                       (coe v19)
                                                       (coe
                                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                          (coe MAlonzo.Code.Once.Type.C_pure_34))
                                                       (coe v22))
                                                    (coe v11) (coe v13)) in
                                       coe
                                         (let v25
                                                = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                       (coe
                                                          d_check'45'complete_3824 (coe v0)
                                                          (coe v18)
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                             (coe v19)
                                                             (coe
                                                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Many_10)
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_pure_34))
                                                             (coe v22))
                                                          (coe v11) (coe v13))) in
                                          coe
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Syntax.C_fork''_478 v11
                                                  v12 v24
                                                  (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                     (coe
                                                        d_check'45'complete_3824 (coe v0) (coe v16)
                                                        (coe
                                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                           (coe v19)
                                                           (coe
                                                              MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.C_pure_34))
                                                           (coe v23))
                                                        (coe v12) (coe v14))))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     addInt (coe (1 :: Integer))
                                                     (coe
                                                        MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                        (coe v25)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                              (coe
                                                                 d_check'45'complete_3824 (coe v0)
                                                                 (coe v16)
                                                                 (coe
                                                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                    (coe v19)
                                                                    (coe
                                                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                       (coe
                                                                          MAlonzo.Code.Once.Type.C_Many_10)
                                                                       (coe
                                                                          MAlonzo.Code.Once.Type.C_pure_34))
                                                                    (coe v23))
                                                                 (coe v12) (coe v14))))))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                              (coe
                                                                 d_check'45'complete_3824 (coe v0)
                                                                 (coe v16)
                                                                 (coe
                                                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                    (coe v19)
                                                                    (coe
                                                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                       (coe
                                                                          MAlonzo.Code.Once.Type.C_Many_10)
                                                                       (coe
                                                                          MAlonzo.Code.Once.Type.C_pure_34))
                                                                    (coe v23))
                                                                 (coe v12) (coe v14)))))
                                                     erased))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'curry'45'check_494 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v14 v15 v16
                      -> case coe v16 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v17 v18 v19
                             -> let v20
                                      = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             d_check'45'complete_3824 (coe v0) (coe v13)
                                             (coe
                                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                (coe
                                                   MAlonzo.Code.Once.Type.C__'42'__122 (coe v14)
                                                   (coe v17))
                                                (coe
                                                   MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                   (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                   (coe MAlonzo.Code.Once.Type.C_pure_34))
                                                (coe v19))
                                             (coe v3) (coe v11)) in
                                coe
                                  (let v21
                                         = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe
                                                   d_check'45'complete_3824 (coe v0) (coe v13)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C__'42'__122
                                                         (coe v14) (coe v17))
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                         (coe MAlonzo.Code.Once.Type.C_pure_34))
                                                      (coe v19))
                                                   (coe v3) (coe v11))) in
                                   coe
                                     (let v22
                                            = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                      (coe
                                                         d_check'45'complete_3824 (coe v0) (coe v13)
                                                         (coe
                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                            (coe
                                                               MAlonzo.Code.Once.Type.C__'42'__122
                                                               (coe v14) (coe v17))
                                                            (coe
                                                               MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                               (coe
                                                                  MAlonzo.Code.Once.Type.C_Many_10)
                                                               (coe
                                                                  MAlonzo.Code.Once.Type.C_pure_34))
                                                            (coe v19))
                                                         (coe v3) (coe v11)))) in
                                      coe
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe MAlonzo.Code.Once.Surface.Syntax.C_curry''_492 v20)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                              (coe addInt (coe (1 :: Integer)) (coe v21))
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v22) erased)))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'cata'45'check_506 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v14 v15 v16
                      -> case coe v14 of
                           MAlonzo.Code.Once.Type.C_μ'45'type_128 v17
                             -> case coe v15 of
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 v18 v19
                                    -> coe
                                         seq (coe v19)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               MAlonzo.Code.Once.Surface.Syntax.C_cata_504 v10
                                               (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                  (coe
                                                     d_check'45'complete_3824
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_368
                                                        (coe (0 :: Integer))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                                        (coe
                                                           MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                                        (coe (0 :: Integer))
                                                        (coe
                                                           MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                                           (coe v0))
                                                        (coe
                                                           MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364
                                                           (coe v0))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                                     (coe v13)
                                                     (coe
                                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                        (coe
                                                           MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                           (coe v17) (coe v16))
                                                        (coe
                                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                           (coe v19))
                                                        (coe v16))
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)
                                                     (coe v11))))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  addInt (coe (1 :: Integer))
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                        (coe
                                                           d_check'45'complete_3824
                                                           (coe
                                                              MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_368
                                                              (coe (0 :: Integer))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                                              (coe
                                                                 MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                                              (coe (0 :: Integer))
                                                              (coe
                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                                                 (coe v0))
                                                              (coe
                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364
                                                                 (coe v0))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                                           (coe v13)
                                                           (coe
                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                                 (coe v17) (coe v16))
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                 (coe
                                                                    MAlonzo.Code.Once.Type.C_Many_10)
                                                                 (coe v19))
                                                              (coe v16))
                                                           (coe
                                                              MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)
                                                           (coe v11)))))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                     (coe v0))
                                                  erased)))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_516 v9
        -> coe du_iFromInfer_3708 (coe v0) (coe v1) (coe v2) (coe v9)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_534 v11 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v15 v16
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v17 v18 v19
                      -> case coe v18 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v20 v21
                             -> coe
                                  du_check'45'complete'45'RLam_2084 (coe v0) (coe v15) (coe v16)
                                  (coe v17) (coe v20) (coe v11) (coe v19)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_550 v10 v11 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__122 v16 v17
                      -> let v18
                               = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_check'45'complete_3824 (coe v0) (coe v14) (coe v16)
                                      (coe v10) (coe v12)) in
                         coe
                           (let v19
                                  = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            d_check'45'complete_3824 (coe v0) (coe v14) (coe v16)
                                            (coe v10) (coe v12))) in
                            coe
                              (coe
                                 du_pair'45'lit'45'reduce_3764 (coe v10) (coe v11) (coe v18)
                                 (coe v19)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       d_check'45'complete_3824 (coe v0) (coe v15) (coe v17)
                                       (coe v11) (coe v13)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          d_check'45'complete_3824 (coe v0) (coe v15) (coe v17)
                                          (coe v11) (coe v13))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             d_check'45'complete_3824 (coe v0) (coe v15) (coe v17)
                                             (coe v11) (coe v13)))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_560 v8 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_128 v13
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'In_2250
                           (coe v0) (coe v12) (coe v13) (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_572 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'apply_2288
                    (coe v0) (coe v12) (coe v7) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_584 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v13 v14
                      -> coe
                           du_completeness'45'gap'45'inl'45'app'45'check'45'eq_3068 (coe v0)
                           (coe v12) (coe v13)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_596 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v13 v14
                      -> coe
                           du_completeness'45'gap'45'inr'45'app'45'check'45'eq_3116 (coe v0)
                           (coe v12) (coe v14)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_606 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    du_completeness'45'gap'45'initial'45'app'45'check'45'eq_3162
                    (coe v0) (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_618 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v11 v12 v13
               -> coe
                    d_subsume'45'complete_3842 (coe v0) (coe v1) (coe v11) (coe v13)
                    (coe v3) (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_634 v8 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> coe
                    d_completeness'45'gap'45'arg'45'driven'45'app'45'check_3430 v0 v15
                    v16 v8 v2 v10 v11 erased v13 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_648 v8 v9 v10 v17
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v18
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'poly_3890
                    (coe v0) (coe v18)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.subsume-complete
d_subsume'45'complete_3842 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_subsume'45'complete_3842 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'check_366
        -> coe
             MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'id_1438
             (coe v0) (coe v2)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'check_376
        -> coe
             MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'fst_1554
             (coe v0) (coe v3)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'check_386
        -> coe
             MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'snd_1658
             (coe v0) (coe v3)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'morph'45'check_394
        -> coe
             MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'terminal_1760
             (coe v0)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'morph'45'check_402
        -> coe
             MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'initial_1894
             (coe v0)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'morph'45'check_412
        -> coe
             MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'inl_1962
             (coe v0) (coe v2)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'morph'45'check_422
        -> coe
             MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'inr_2066
             (coe v0) (coe v2)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check_442 v10 v13 v14 v16 v17
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v20 v21
                      -> let v22
                               = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_subsume'45'complete_3842 (coe v0) (coe v21) (coe v10)
                                      (coe v3) (coe v13) (coe v16)) in
                         coe
                           (let v23
                                  = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            d_subsume'45'complete_3842 (coe v0) (coe v21) (coe v10)
                                            (coe v3) (coe v13) (coe v16))) in
                            coe
                              (let v24
                                     = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  d_subsume'45'complete_3842 (coe v0) (coe v21)
                                                  (coe v10) (coe v3) (coe v13) (coe v16)))) in
                               coe
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_comp''_444 v13 v14 v10 v22
                                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             d_subsume'45'complete_3842 (coe v0) (coe v19) (coe v2)
                                             (coe v10) (coe v14) (coe v17))))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                       (coe
                                          addInt (coe (1 :: Integer))
                                          (coe
                                             MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v23)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                   (coe
                                                      d_subsume'45'complete_3842 (coe v0) (coe v19)
                                                      (coe v2) (coe v10) (coe v14) (coe v17))))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v24)
                                          erased)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case'45'copair'45'check_462 v13 v14 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v19 v20
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'43'__124 v21 v22
                             -> let v23
                                      = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             d_subsume'45'complete_3842 (coe v0) (coe v20) (coe v21)
                                             (coe v3) (coe v13) (coe v15)) in
                                coe
                                  (let v24
                                         = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe
                                                   d_subsume'45'complete_3842 (coe v0) (coe v20)
                                                   (coe v21) (coe v3) (coe v13) (coe v15))) in
                                   coe
                                     (let v25
                                            = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                      (coe
                                                         d_subsume'45'complete_3842 (coe v0)
                                                         (coe v20) (coe v21) (coe v3) (coe v13)
                                                         (coe v15)))) in
                                      coe
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.C_copair''_462 v13
                                              v14 v23
                                              (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                 (coe
                                                    d_subsume'45'complete_3842 (coe v0) (coe v18)
                                                    (coe v22) (coe v3) (coe v14) (coe v16))))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                              (coe
                                                 addInt (coe (1 :: Integer))
                                                 (coe
                                                    MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                    (coe v24)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                          (coe
                                                             d_subsume'45'complete_3842 (coe v0)
                                                             (coe v18) (coe v22) (coe v3) (coe v14)
                                                             (coe v16))))))
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v25) erased)))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'morph'45'check_480 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
                      -> case coe v3 of
                           MAlonzo.Code.Once.Type.C__'42'__122 v20 v21
                             -> let v22
                                      = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             d_check'45'complete_3824 (coe v0) (coe v19)
                                             (coe
                                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                (coe v2)
                                                (coe
                                                   MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                   (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                   (coe MAlonzo.Code.Once.Type.C_pure_34))
                                                (coe v20))
                                             (coe v12) (coe v14)) in
                                coe
                                  (let v23
                                         = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                (coe
                                                   d_check'45'complete_3824 (coe v0) (coe v19)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                      (coe v2)
                                                      (coe
                                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                         (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                         (coe MAlonzo.Code.Once.Type.C_pure_34))
                                                      (coe v20))
                                                   (coe v12) (coe v14))) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe
                                           MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
                                           (coe
                                              MAlonzo.Code.Once.Surface.Syntax.C_fork''_478 v12 v13
                                              v22
                                              (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                 (coe
                                                    d_check'45'complete_3824 (coe v0) (coe v17)
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                       (coe v2)
                                                       (coe
                                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                          (coe MAlonzo.Code.Once.Type.C_pure_34))
                                                       (coe v21))
                                                    (coe v13) (coe v15)))))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe
                                              addInt (coe (1 :: Integer))
                                              (coe
                                                 MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v23)
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                       (coe
                                                          d_check'45'complete_3824 (coe v0)
                                                          (coe v17)
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                             (coe v2)
                                                             (coe
                                                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Many_10)
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_pure_34))
                                                             (coe v21))
                                                          (coe v13) (coe v15))))))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                       (coe
                                                          d_check'45'complete_3824 (coe v0)
                                                          (coe v17)
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                             (coe v2)
                                                             (coe
                                                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Many_10)
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_pure_34))
                                                             (coe v21))
                                                          (coe v13) (coe v15)))))
                                              erased))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'curry'45'check_494 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v15 v16 v17
                      -> let v18
                               = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_check'45'complete_3824 (coe v0) (coe v14)
                                      (coe
                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                         (coe
                                            MAlonzo.Code.Once.Type.C__'42'__122 (coe v2) (coe v15))
                                         (coe
                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                            (coe MAlonzo.Code.Once.Type.C_Many_10)
                                            (coe MAlonzo.Code.Once.Type.C_pure_34))
                                         (coe v17))
                                      (coe v4) (coe v12)) in
                         coe
                           (let v19
                                  = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            d_check'45'complete_3824 (coe v0) (coe v14)
                                            (coe
                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                               (coe
                                                  MAlonzo.Code.Once.Type.C__'42'__122 (coe v2)
                                                  (coe v15))
                                               (coe
                                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                  (coe MAlonzo.Code.Once.Type.C_pure_34))
                                               (coe v17))
                                            (coe v4) (coe v12))) in
                            coe
                              (let v20
                                     = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  d_check'45'complete_3824 (coe v0) (coe v14)
                                                  (coe
                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                     (coe
                                                        MAlonzo.Code.Once.Type.C__'42'__122 (coe v2)
                                                        (coe v15))
                                                     (coe
                                                        MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                        (coe MAlonzo.Code.Once.Type.C_pure_34))
                                                     (coe v17))
                                                  (coe v4) (coe v12)))) in
                               coe
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe
                                       MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
                                       (coe MAlonzo.Code.Once.Surface.Syntax.C_curry''_492 v18))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                       (coe addInt (coe (1 :: Integer)) (coe v19))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v20)
                                          erased)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'cata'45'check_506 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_128 v15
                      -> let v16
                               = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      d_subsume'45'complete_3842
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_368
                                         (coe (0 :: Integer))
                                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                         (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                         (coe (0 :: Integer))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                            (coe v0))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364
                                            (coe v0))
                                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                      (coe v14)
                                      (coe
                                         MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v15)
                                         (coe v3))
                                      (coe v3) (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)
                                      (coe v12)) in
                         coe
                           (let v17
                                  = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            d_subsume'45'complete_3842
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_368
                                               (coe (0 :: Integer))
                                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                               (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                               (coe (0 :: Integer))
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                                  (coe v0))
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364
                                                  (coe v0))
                                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                            (coe v14)
                                            (coe
                                               MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                               (coe v15) (coe v3))
                                            (coe v3)
                                            (coe MAlonzo.Code.Once.Surface.Context.C_'91''93'_62)
                                            (coe v12))) in
                            coe
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe MAlonzo.Code.Once.Surface.Syntax.C_cata_504 v11 v16)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe addInt (coe (1 :: Integer)) (coe v17))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                          (coe v0))
                                       erased))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_516 v10
        -> coe
             du_iFromInferEff_3782 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_534 v12 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v16 v17
               -> coe
                    du_check'45'complete'45'RLam'45'eff_2174 (coe v0) (coe v16)
                    (coe v17) (coe v2) (coe v12) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_572 v8 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> coe
                    du_iFromInferEff_3782 (coe v0)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                          (coe ("apply" :: Data.Text.Text)))
                       (coe v13))
                    (coe v2) (coe v3)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_324
                       v8 v10 v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_606 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'initial'45'eff_4928
                    (coe v0) (coe v12)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_634 v9 v11 v12 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> coe
                    d_completeness'45'gap'45'arg'45'driven'45'app'45'check'45'eff_3454
                    v0 v16 v17 v9 v2 v3 v11 v12 erased v14 v15
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_648 v9 v10 v11 v18
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v19
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'poly_3890
                    (coe v0) (coe v19)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
