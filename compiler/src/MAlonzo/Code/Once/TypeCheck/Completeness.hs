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
import qualified MAlonzo.Code.Agda.Builtin.Maybe
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
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.IRTy.WF
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Elaborate
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Surface.Thinning
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
                                        MAlonzo.Code.Once.IR.C_SigOp_154 (coe v5) (coe v7)
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.d_ext'45'arrow'45'info_2558
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
                                        MAlonzo.Code.Once.IR.C_SigOp_154 (coe v4) (coe v6)
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Elaborate.d_ext'45'resolved'45'info_2570
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
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
              (coe v0) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v6 v7 v8 v9 v10
                  -> let v11
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
                    = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_2040
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
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
              (coe v0) (coe v2) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                  -> let v12
                           = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
                             MAlonzo.Code.Once.Surface.Syntax.du_svar'8594'expr_460 (coe v2))
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
                 = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
                     (coe v0) (coe v2) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                         -> coe
                              seq (coe v7)
                              (let v12
                                     = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_2040
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
                              = MAlonzo.Code.Once.TypeCheck.Elaborate.d_decideLeq_1742
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
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_2040
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
                              = MAlonzo.Code.Once.TypeCheck.Elaborate.d_decideLeq_1742
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
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
              (coe v0) (coe v1) in
    coe
      (case coe v7 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
           -> case coe v8 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v10 v11 v12 v13 v14
                  -> case coe v10 of
                       MAlonzo.Code.Once.Type.C__'43'__124 v15 v16
                         -> let v17
                                  = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
                                                          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
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
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
              (coe v0) (coe v1) in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
           -> case coe v6 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v8 v9 v10 v11 v12
                  -> let v13
                           = coe
                               MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_2040
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
  MAlonzo.Code.Once.TypeCheck.Classify.T_AppHeadView_1020 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_viewBridge_2494 = erased
-- Once.TypeCheck.Completeness.otherBridge
d_otherBridge_2506 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Classify.T_PolyBuiltinApp_990 ->
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
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024
              (coe v0) (coe v1) in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
                  -> let v12
                           = coe
                               MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_2040
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
                               (coe MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'id_1274) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'id_1274
                            -> let v7
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
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
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'fst_1276
                            -> let v7
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
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
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'snd_1278
                            -> let v7
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
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
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'terminal_1280
                            -> let v7
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
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
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'initial_1282
                            -> let v7
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
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
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inl_1284
                            -> let v7
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
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
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inr_1286
                            -> let v7
                                     = coe
                                         MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
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
                          MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'other_1290
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
                                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_56)) in
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
                                                              MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
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
                                                       MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'fst_1276)
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
                                                                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'snd_1278)
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
                                                                                               MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'terminal_1280)
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
                                                                                                                   MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'initial_1282)
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
                                                                                                                                       MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inl_1284)
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
                                                                                                                                                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inr_1286)
                                                                                                                                                 else coe
                                                                                                                                                        seq
                                                                                                                                                        (coe
                                                                                                                                                           v23)
                                                                                                                                                        (coe
                                                                                                                                                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'other_1290)
                                                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                      _ -> MAlonzo.RTE.mazUnreachableError)) in
                      coe
                        (case coe v6 of
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'id_1274
                             -> let v7
                                      = coe
                                          MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
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
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'fst_1276
                             -> let v7
                                      = coe
                                          MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
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
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'snd_1278
                             -> let v7
                                      = coe
                                          MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
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
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'terminal_1280
                             -> let v7
                                      = coe
                                          MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
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
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'initial_1282
                             -> let v7
                                      = coe
                                          MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
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
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inl_1284
                             -> let v7
                                      = coe
                                          MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
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
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'inr_1286
                             -> let v7
                                      = coe
                                          MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
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
                           MAlonzo.Code.Once.TypeCheck.Classify.C_bbc'45'other_1290
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
                                                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_56)) in
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
                                                               MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
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
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_2040
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
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_2040
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
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_2040
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
-- Once.TypeCheck.Completeness.closed-lift-aux-lifts
d_closed'45'lift'45'aux'45'lifts_3224 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  Maybe MAlonzo.Code.Once.TypeCheck.Raw.T_ClosedLiftShape_100 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_closed'45'lift'45'aux'45'lifts_3224 v0 ~v1 v2 v3 ~v4 ~v5 v6 v7 v8
                                      ~v9 v10 v11 v12 ~v13 ~v14 ~v15 ~v16 ~v17
  = du_closed'45'lift'45'aux'45'lifts_3224
      v0 v2 v3 v6 v7 v8 v10 v11 v12
du_closed'45'lift'45'aux'45'lifts_3224 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  Maybe MAlonzo.Code.Once.TypeCheck.Raw.T_ClosedLiftShape_100 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_closed'45'lift'45'aux'45'lifts_3224 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v7 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
        -> coe
             seq (coe v9)
             (coe
                seq (coe v10)
                (coe
                   seq (coe v8)
                   (coe
                      seq (coe v6)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe
                            MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
                            (coe
                               MAlonzo.Code.Once.Surface.Syntax.C_lam_32
                               (coe MAlonzo.Code.Once.Type.C_Zero_6)
                               (coe
                                  MAlonzo.Code.Once.Surface.Thinning.du_weaken_1024
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v0))
                                  (coe v2) (coe v1) (coe MAlonzo.Code.Once.Type.C_Many_10)
                                  (coe v3))))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                            (coe addInt (coe (1 :: Integer)) (coe v4))
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) erased))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.embedOrSubsume-lifts
d_embedOrSubsume'45'lifts_3324 ::
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
d_embedOrSubsume'45'lifts_3324 v0 v1 v2 v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_embedOrSubsume'45'lifts_3324 v0 v1 v2 v3 v4
du_embedOrSubsume'45'lifts_3324 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_embedOrSubsume'45'lifts_3324 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v5 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v7 v8 v9 v10 v11
               -> let v12
                        = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                            (coe
                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v2)
                               (coe
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                                  (coe MAlonzo.Code.Once.Type.C_pure_34))
                               (coe v3))
                            (coe v7) in
                  coe
                    (case coe v12 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                         -> if coe v13
                              then coe
                                     seq (coe v14)
                                     (coe
                                        seq (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                        (let v15
                                               = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                   (coe v2) (coe v2) in
                                         coe
                                           (case coe v15 of
                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                -> if coe v16
                                                     then coe
                                                            seq (coe v17)
                                                            (let v18
                                                                   = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                                       (coe v3) (coe v3) in
                                                             coe
                                                               (case coe v18 of
                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v19 v20
                                                                    -> if coe v19
                                                                         then case coe v20 of
                                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v21
                                                                                  -> coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       (coe
                                                                                          MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
                                                                                          v9)
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                          (coe v10)
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                             (coe
                                                                                                v11)
                                                                                             erased))
                                                                                _ -> coe
                                                                                       seq (coe v19)
                                                                                       (coe
                                                                                          seq
                                                                                          (coe v20)
                                                                                          (coe
                                                                                             MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
                                                                         else (case coe v20 of
                                                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                   -> coe
                                                                                        MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                                 _ -> coe
                                                                                        seq
                                                                                        (coe v19)
                                                                                        (coe
                                                                                           seq
                                                                                           (coe v20)
                                                                                           (coe
                                                                                              MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)))
                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                                     else coe
                                                            seq (coe v17)
                                                            (coe
                                                               MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                              _ -> MAlonzo.RTE.mazUnreachableError)))
                              else (case coe v7 of
                                      MAlonzo.Code.Once.Type.C_Unit_118
                                        -> coe
                                             seq (coe v14)
                                             (coe
                                                du_closed'45'lift'45'aux'45'lifts_3224 (coe v0)
                                                (coe v7) (coe v2) (coe v9) (coe v10) (coe v11)
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Raw.d_closedLiftShape'63'_158
                                                   (coe v1))
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                   (coe v7) (coe v3))
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Context.du_zeroUsage'63'_78
                                                   (coe v8)))
                                      MAlonzo.Code.Once.Type.C_Void_120
                                        -> coe
                                             seq (coe v14)
                                             (coe
                                                du_closed'45'lift'45'aux'45'lifts_3224 (coe v0)
                                                (coe v7) (coe v2) (coe v9) (coe v10) (coe v11)
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Raw.d_closedLiftShape'63'_158
                                                   (coe v1))
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                   (coe v7) (coe v3))
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Context.du_zeroUsage'63'_78
                                                   (coe v8)))
                                      MAlonzo.Code.Once.Type.C__'42'__122 v15 v16
                                        -> coe
                                             seq (coe v14)
                                             (coe
                                                du_closed'45'lift'45'aux'45'lifts_3224 (coe v0)
                                                (coe v7) (coe v2) (coe v9) (coe v10) (coe v11)
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Raw.d_closedLiftShape'63'_158
                                                   (coe v1))
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                   (coe v7) (coe v3))
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Context.du_zeroUsage'63'_78
                                                   (coe v8)))
                                      MAlonzo.Code.Once.Type.C__'43'__124 v15 v16
                                        -> coe
                                             seq (coe v14)
                                             (coe
                                                du_closed'45'lift'45'aux'45'lifts_3224 (coe v0)
                                                (coe v7) (coe v2) (coe v9) (coe v10) (coe v11)
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Raw.d_closedLiftShape'63'_158
                                                   (coe v1))
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                   (coe v7) (coe v3))
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Context.du_zeroUsage'63'_78
                                                   (coe v8)))
                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v15 v16 v17
                                        -> case coe v16 of
                                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v18 v19
                                               -> case coe v18 of
                                                    MAlonzo.Code.Once.Type.C_Zero_6
                                                      -> coe
                                                           seq (coe v14)
                                                           (coe
                                                              du_closed'45'lift'45'aux'45'lifts_3224
                                                              (coe v0) (coe v7) (coe v2) (coe v9)
                                                              (coe v10) (coe v11)
                                                              (coe
                                                                 MAlonzo.Code.Once.TypeCheck.Raw.d_closedLiftShape'63'_158
                                                                 (coe v1))
                                                              (coe
                                                                 MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                                 (coe v7) (coe v3))
                                                              (coe
                                                                 MAlonzo.Code.Once.Surface.Context.du_zeroUsage'63'_78
                                                                 (coe v8)))
                                                    MAlonzo.Code.Once.Type.C_One_8
                                                      -> coe
                                                           seq (coe v14)
                                                           (coe
                                                              du_closed'45'lift'45'aux'45'lifts_3224
                                                              (coe v0) (coe v7) (coe v2) (coe v9)
                                                              (coe v10) (coe v11)
                                                              (coe
                                                                 MAlonzo.Code.Once.TypeCheck.Raw.d_closedLiftShape'63'_158
                                                                 (coe v1))
                                                              (coe
                                                                 MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                                 (coe v7) (coe v3))
                                                              (coe
                                                                 MAlonzo.Code.Once.Surface.Context.du_zeroUsage'63'_78
                                                                 (coe v8)))
                                                    MAlonzo.Code.Once.Type.C_Many_10
                                                      -> case coe v19 of
                                                           MAlonzo.Code.Once.Type.C_pure_34
                                                             -> case coe v14 of
                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                    -> let v21
                                                                             = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                                                 (coe v2)
                                                                                 (coe v15) in
                                                                       coe
                                                                         (let v22
                                                                                = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                                                    (coe v3)
                                                                                    (coe v17) in
                                                                          coe
                                                                            (case coe v21 of
                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                                                                 -> if coe v23
                                                                                      then coe
                                                                                             seq
                                                                                             (coe
                                                                                                v24)
                                                                                             (case coe
                                                                                                     v22 of
                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v25 v26
                                                                                                  -> if coe
                                                                                                          v25
                                                                                                       then coe
                                                                                                              seq
                                                                                                              (coe
                                                                                                                 v26)
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                                                                       else coe
                                                                                                              seq
                                                                                                              (coe
                                                                                                                 v26)
                                                                                                              (coe
                                                                                                                 du_closed'45'lift'45'aux'45'lifts_3224
                                                                                                                 (coe
                                                                                                                    v0)
                                                                                                                 (coe
                                                                                                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                                    (coe
                                                                                                                       v2)
                                                                                                                    (coe
                                                                                                                       v16)
                                                                                                                    (coe
                                                                                                                       v17))
                                                                                                                 (coe
                                                                                                                    v2)
                                                                                                                 (coe
                                                                                                                    v9)
                                                                                                                 (coe
                                                                                                                    v10)
                                                                                                                 (coe
                                                                                                                    v11)
                                                                                                                 (coe
                                                                                                                    MAlonzo.Code.Once.TypeCheck.Raw.d_closedLiftShape'63'_158
                                                                                                                    (coe
                                                                                                                       v1))
                                                                                                                 (coe
                                                                                                                    MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                                                                                    (coe
                                                                                                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                                       (coe
                                                                                                                          v2)
                                                                                                                       (coe
                                                                                                                          v16)
                                                                                                                       (coe
                                                                                                                          v17))
                                                                                                                    (coe
                                                                                                                       v3))
                                                                                                                 (coe
                                                                                                                    MAlonzo.Code.Once.Surface.Context.du_zeroUsage'63'_78
                                                                                                                    (coe
                                                                                                                       v8)))
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                      else coe
                                                                                             seq
                                                                                             (coe
                                                                                                v24)
                                                                                             (coe
                                                                                                du_closed'45'lift'45'aux'45'lifts_3224
                                                                                                (coe
                                                                                                   v0)
                                                                                                (coe
                                                                                                   v7)
                                                                                                (coe
                                                                                                   v2)
                                                                                                (coe
                                                                                                   v9)
                                                                                                (coe
                                                                                                   v10)
                                                                                                (coe
                                                                                                   v11)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.TypeCheck.Raw.d_closedLiftShape'63'_158
                                                                                                   (coe
                                                                                                      v1))
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                                                                   (coe
                                                                                                      v7)
                                                                                                   (coe
                                                                                                      v3))
                                                                                                (coe
                                                                                                   MAlonzo.Code.Once.Surface.Context.du_zeroUsage'63'_78
                                                                                                   (coe
                                                                                                      v8)))
                                                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                           MAlonzo.Code.Once.Type.C_eff_36
                                                             -> coe
                                                                  seq (coe v14)
                                                                  (let v20
                                                                         = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                                             (coe v2) (coe v15) in
                                                                   coe
                                                                     (case coe v20 of
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                                          -> if coe v21
                                                                               then coe
                                                                                      seq (coe v22)
                                                                                      (let v23
                                                                                             = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                                                                 (coe
                                                                                                    v3)
                                                                                                 (coe
                                                                                                    v17) in
                                                                                       coe
                                                                                         (case coe
                                                                                                 v23 of
                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v24 v25
                                                                                              -> coe
                                                                                                   seq
                                                                                                   (coe
                                                                                                      v24)
                                                                                                   (coe
                                                                                                      seq
                                                                                                      (coe
                                                                                                         v25)
                                                                                                      (coe
                                                                                                         du_closed'45'lift'45'aux'45'lifts_3224
                                                                                                         (coe
                                                                                                            v0)
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                            (coe
                                                                                                               v2)
                                                                                                            (coe
                                                                                                               v16)
                                                                                                            (coe
                                                                                                               v17))
                                                                                                         (coe
                                                                                                            v2)
                                                                                                         (coe
                                                                                                            v9)
                                                                                                         (coe
                                                                                                            v10)
                                                                                                         (coe
                                                                                                            v11)
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.TypeCheck.Raw.d_closedLiftShape'63'_158
                                                                                                            (coe
                                                                                                               v1))
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                                                               (coe
                                                                                                                  v2)
                                                                                                               (coe
                                                                                                                  v16)
                                                                                                               (coe
                                                                                                                  v17))
                                                                                                            (coe
                                                                                                               v3))
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Once.Surface.Context.du_zeroUsage'63'_78
                                                                                                            (coe
                                                                                                               v8))))
                                                                                            _ -> MAlonzo.RTE.mazUnreachableError))
                                                                               else coe
                                                                                      seq (coe v22)
                                                                                      (coe
                                                                                         du_closed'45'lift'45'aux'45'lifts_3224
                                                                                         (coe v0)
                                                                                         (coe v7)
                                                                                         (coe v2)
                                                                                         (coe v9)
                                                                                         (coe v10)
                                                                                         (coe v11)
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.TypeCheck.Raw.d_closedLiftShape'63'_158
                                                                                            (coe
                                                                                               v1))
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                                                            (coe v7)
                                                                                            (coe
                                                                                               v3))
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.Surface.Context.du_zeroUsage'63'_78
                                                                                            (coe
                                                                                               v8)))
                                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                             _ -> MAlonzo.RTE.mazUnreachableError
                                      MAlonzo.Code.Once.Type.C_μ'45'type_128 v15
                                        -> coe
                                             seq (coe v14)
                                             (coe
                                                du_closed'45'lift'45'aux'45'lifts_3224 (coe v0)
                                                (coe v7) (coe v2) (coe v9) (coe v10) (coe v11)
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Raw.d_closedLiftShape'63'_158
                                                   (coe v1))
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                   (coe v7) (coe v3))
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Context.du_zeroUsage'63'_78
                                                   (coe v8)))
                                      MAlonzo.Code.Once.Type.C_ν'45'type_130 v15
                                        -> coe
                                             seq (coe v14)
                                             (coe
                                                du_closed'45'lift'45'aux'45'lifts_3224 (coe v0)
                                                (coe v7) (coe v2) (coe v9) (coe v10) (coe v11)
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Raw.d_closedLiftShape'63'_158
                                                   (coe v1))
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                   (coe v7) (coe v3))
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Context.du_zeroUsage'63'_78
                                                   (coe v8)))
                                      MAlonzo.Code.Once.Type.C_Int_132
                                        -> coe
                                             seq (coe v14)
                                             (coe
                                                du_closed'45'lift'45'aux'45'lifts_3224 (coe v0)
                                                (coe v7) (coe v2) (coe v9) (coe v10) (coe v11)
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Raw.d_closedLiftShape'63'_158
                                                   (coe v1))
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                   (coe v7) (coe v3))
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Context.du_zeroUsage'63'_78
                                                   (coe v8)))
                                      MAlonzo.Code.Once.Type.C_Float_134
                                        -> coe
                                             seq (coe v14)
                                             (coe
                                                du_closed'45'lift'45'aux'45'lifts_3224 (coe v0)
                                                (coe v7) (coe v2) (coe v9) (coe v10) (coe v11)
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Raw.d_closedLiftShape'63'_158
                                                   (coe v1))
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                   (coe v7) (coe v3))
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Context.du_zeroUsage'63'_78
                                                   (coe v8)))
                                      MAlonzo.Code.Once.Type.C_Str_136
                                        -> coe
                                             seq (coe v14)
                                             (coe
                                                du_closed'45'lift'45'aux'45'lifts_3224 (coe v0)
                                                (coe v7) (coe v2) (coe v9) (coe v10) (coe v11)
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Raw.d_closedLiftShape'63'_158
                                                   (coe v1))
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                   (coe v7) (coe v3))
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Context.du_zeroUsage'63'_78
                                                   (coe v8)))
                                      MAlonzo.Code.Once.Type.C_Buffer_138
                                        -> coe
                                             seq (coe v14)
                                             (coe
                                                du_closed'45'lift'45'aux'45'lifts_3224 (coe v0)
                                                (coe v7) (coe v2) (coe v9) (coe v10) (coe v11)
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Raw.d_closedLiftShape'63'_158
                                                   (coe v1))
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                                                   (coe v7) (coe v3))
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Context.du_zeroUsage'63'_78
                                                   (coe v8)))
                                      _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.embedOrSubsume-closed-pure
d_embedOrSubsume'45'closed'45'pure_4126 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_ClosedLiftShape_100 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_embedOrSubsume'45'closed'45'pure_4126 v0 ~v1 v2 v3 ~v4 v5 v6 v7
                                        ~v8
  = du_embedOrSubsume'45'closed'45'pure_4126 v0 v2 v3 v5 v6 v7
du_embedOrSubsume'45'closed'45'pure_4126 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_embedOrSubsume'45'closed'45'pure_4126 v0 v1 v2 v3 v4 v5
  = let v6
          = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
              (coe
                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v1)
                 (coe
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                    (coe MAlonzo.Code.Once.Type.C_pure_34))
                 (coe v2))
              (coe v2) in
    coe
      (case coe v6 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
           -> coe
                seq (coe v7)
                (coe
                   seq (coe v8)
                   (let v9
                          = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
                              (coe v2) (coe v2) in
                    coe
                      (case coe v9 of
                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                           -> if coe v10
                                then coe
                                       seq (coe v11)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                          (coe
                                             MAlonzo.Code.Once.Surface.Syntax.C_lam_32
                                             (coe MAlonzo.Code.Once.Type.C_Zero_6)
                                             (coe
                                                MAlonzo.Code.Once.Surface.Thinning.du_weaken_1024
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                                   (coe v0))
                                                (coe v1) (coe v2)
                                                (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v3)))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                             (coe addInt (coe (1 :: Integer)) (coe v4))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                                erased)))
                                else coe
                                       seq (coe v11)
                                       (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                         _ -> MAlonzo.RTE.mazUnreachableError)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Completeness.embedOrSubsume-closed
d_embedOrSubsume'45'closed_4222 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_ClosedLiftShape_100 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_embedOrSubsume'45'closed_4222 v0 v1 v2 v3 v4 ~v5 v6 v7 v8 v9
  = du_embedOrSubsume'45'closed_4222 v0 v1 v2 v3 v4 v6 v7 v8 v9
du_embedOrSubsume'45'closed_4222 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_embedOrSubsume'45'closed_4222 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v4 of
      MAlonzo.Code.Once.Type.C_pure_34
        -> coe
             du_embedOrSubsume'45'closed'45'pure_4126 (coe v0) (coe v2) (coe v3)
             (coe v5) (coe v6) (coe v7)
      MAlonzo.Code.Once.Type.C_eff_36
        -> coe
             du_embedOrSubsume'45'lifts_3324 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 (coe v3)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                      (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0)))
                   (coe v5) (coe v6) (coe v7))
                (coe v8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.checkElab-closed-lift
d_checkElab'45'closed'45'lift_4276 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_ClosedLiftShape_100 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkElab'45'closed'45'lift_4276 v0 v1 ~v2 v3 v4 v5 ~v6 ~v7 ~v8
                                   ~v9
  = du_checkElab'45'closed'45'lift_4276 v0 v1 v3 v4 v5
du_checkElab'45'closed'45'lift_4276 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_ClosedLiftShape_100 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkElab'45'closed'45'lift_4276 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'var_104
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v6
               -> let v7
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v7 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe v6))
                            (coe
                               MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                               (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                               (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v6)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                  ("unit" :: Data.Text.Text))) in
                  coe
                    (case coe v7 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                         -> if coe v8
                              then let v10
                                         = seq
                                             (coe v9)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300
                                                   (coe MAlonzo.Code.Once.Type.C_Unit_118)
                                                   (coe
                                                      MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                                                      (coe
                                                         MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                                                         (coe v0)))
                                                   (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_152)
                                                   (coe (0 :: Integer))
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                      (coe v0)))
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_56)) in
                                   coe
                                     (case coe v10 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                          -> case coe v11 of
                                               MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v13 v14 v15 v16 v17
                                                 -> coe
                                                      du_embedOrSubsume'45'closed_4222 (coe v0)
                                                      (coe v1) (coe v2) (coe v13) (coe v3) (coe v15)
                                                      (coe v16) (coe v17) (coe v12)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              else (let v10
                                          = seq
                                              (coe v9)
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
                                                 (coe v0) (coe v6)
                                                 (coe
                                                    MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal_572
                                                    (coe v0) (coe v6))
                                                 (coe
                                                    MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                                    (coe
                                                       MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                                       (coe v0))
                                                    (coe v6))) in
                                    coe
                                      (case coe v10 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                           -> case coe v11 of
                                                MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v13 v14 v15 v16 v17
                                                  -> coe
                                                       du_embedOrSubsume'45'closed_4222 (coe v0)
                                                       (coe v1) (coe v2) (coe v13) (coe v3)
                                                       (coe v15) (coe v16) (coe v17) (coe v12)
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'qual_110
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v7 v8
               -> let v9
                        = coe
                            MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RQualified'45'aux_2256
                            (coe v0) (coe v7) (coe v8)
                            (coe
                               MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                               (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20 v8
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     ("." :: Data.Text.Text) v7))) in
                  coe
                    (case coe v9 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                         -> case coe v10 of
                              MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v12 v13 v14 v15 v16
                                -> coe
                                     du_embedOrSubsume'45'closed_4222 (coe v0) (coe v1) (coe v2)
                                     (coe v12) (coe v3) (coe v14) (coe v15) (coe v16) (coe v11)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'res_114
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v6
               -> let v7
                        = coe
                            MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RResolved'45'aux_2264
                            (coe v0) (coe v6)
                            (coe
                               MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                               (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                               (coe
                                  MAlonzo.Code.Once.CanonicalName.d_showCanonical_40 (coe v6))) in
                  coe
                    (case coe v7 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                         -> case coe v8 of
                              MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v10 v11 v12 v13 v14
                                -> coe
                                     du_embedOrSubsume'45'closed_4222 (coe v0) (coe v1) (coe v2)
                                     (coe v10) (coe v3) (coe v12) (coe v13) (coe v14) (coe v9)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'let_122
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v8 v9 v10
               -> let v11
                        = coe
                            MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RLet'45'aux_2140
                            (coe v0) (coe v8) (coe v10)
                            (coe
                               MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024 (coe v0)
                               (coe v9)) in
                  coe
                    (case coe v11 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                         -> case coe v12 of
                              MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v14 v15 v16 v17 v18
                                -> coe
                                     du_embedOrSubsume'45'closed_4222 (coe v0) (coe v1) (coe v2)
                                     (coe v14) (coe v3) (coe v16) (coe v17) (coe v18) (coe v13)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'destr_134
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v10 v11 v12 v13 v14
               -> let v15
                        = coe
                            MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RDestruct'45'aux_2176
                            (coe v0) (coe v11) (coe v12) (coe v13) (coe v14)
                            (coe
                               MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024 (coe v0)
                               (coe v10)) in
                  coe
                    (case coe v15 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                         -> case coe v16 of
                              MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v18 v19 v20 v21 v22
                                -> coe
                                     du_embedOrSubsume'45'closed_4222 (coe v0) (coe v1) (coe v2)
                                     (coe v18) (coe v3) (coe v20) (coe v21) (coe v22) (coe v17)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'unit_136
        -> coe
             du_embedOrSubsume'45'closed_4222 (coe v0)
             (coe MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_52) (coe v2)
             (coe MAlonzo.Code.Once.Type.C_Unit_118) (coe v3)
             (coe MAlonzo.Code.Once.Surface.Syntax.C_unit_152)
             (coe (0 :: Integer))
             (coe
                MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
             (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_52)
      MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'str_140
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_58 v6
               -> coe
                    du_embedOrSubsume'45'closed_4222 (coe v0) (coe v1) (coe v2)
                    (coe MAlonzo.Code.Once.Type.C_Str_136) (coe v3)
                    (coe MAlonzo.Code.Once.Surface.Syntax.C_str_190 v6)
                    (coe (0 :: Integer))
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
                    (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'str_48)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'annot_146
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v7 v8
               -> let v9
                        = coe
                            MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RAnnot'45'aux_2064
                            (coe v8)
                            (coe
                               MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_2040
                               (coe v0) (coe v7) (coe v8)) in
                  coe
                    (case coe v9 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                         -> case coe v10 of
                              MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v12 v13 v14 v15 v16
                                -> coe
                                     du_embedOrSubsume'45'closed_4222 (coe v0) (coe v1) (coe v2)
                                     (coe v12) (coe v3) (coe v14) (coe v15) (coe v16) (coe v11)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Raw.C_cls'45'binop_154
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v8 v9 v10
               -> let v11
                        = coe
                            MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RBinOp'45'aux_2130
                            (coe v8)
                            (coe
                               MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024 (coe v0)
                               (coe v9))
                            (coe
                               MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024 (coe v0)
                               (coe v10)) in
                  coe
                    (case coe v11 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                         -> case coe v12 of
                              MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_300 v14 v15 v16 v17 v18
                                -> coe
                                     du_embedOrSubsume'45'closed_4222 (coe v0) (coe v1) (coe v2)
                                     (coe v14) (coe v3) (coe v16) (coe v17) (coe v18) (coe v13)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.completeness-gap-arg-driven-app-check
d_completeness'45'gap'45'arg'45'driven'45'app'45'check_5072
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.Completeness.completeness-gap-arg-driven-app-check"
-- Once.TypeCheck.Completeness.completeness-gap-arg-driven-app-check-eff
d_completeness'45'gap'45'arg'45'driven'45'app'45'check'45'eff_5096
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.Completeness.completeness-gap-arg-driven-app-check-eff"
-- Once.TypeCheck.Completeness.regrade-eff
d_regrade'45'eff_5108 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  Maybe
    MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18
d_regrade'45'eff_5108 ~v0 v1 v2 v3 ~v4 v5
  = du_regrade'45'eff_5108 v1 v2 v3 v5
du_regrade'45'eff_5108 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  Maybe
    MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18
du_regrade'45'eff_5108 v0 v1 v2 v3
  = let v4 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'id_456
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'id_456)
         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'fst_466
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'42'__122 v11 v12
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'fst_466)
                _ -> coe v4
         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'snd_476
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'42'__122 v11 v12
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'snd_476)
                _ -> coe v4
         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'terminal_484
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'terminal_484)
         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'initial_492
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'initial_492)
         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inl_502
           -> case coe v2 of
                MAlonzo.Code.Once.Type.C__'43'__124 v11 v12
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inl_502)
                _ -> coe v4
         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inr_512
           -> case coe v2 of
                MAlonzo.Code.Once.Type.C__'43'__124 v11 v12
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inr_512)
                _ -> coe v4
         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'compose_528 v9 v13 v14
           -> case coe v0 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
                  -> case coe v15 of
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
                         -> let v19
                                  = coe
                                      du_regrade'45'eff_5108 (coe v18) (coe v9) (coe v2)
                                      (coe v13) in
                            coe
                              (let v20
                                     = coe
                                         du_regrade'45'eff_5108 (coe v16) (coe v1) (coe v9)
                                         (coe v14) in
                               coe
                                 (case coe v19 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v21
                                      -> case coe v20 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v22
                                             -> coe
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'compose_528
                                                     v9 v21 v22)
                                           _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                    _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                       _ -> coe v4
                _ -> coe v4
         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'case_544 v12 v13
           -> case coe v0 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
                  -> case coe v14 of
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
                         -> case coe v1 of
                              MAlonzo.Code.Once.Type.C__'43'__124 v18 v19
                                -> let v20
                                         = coe
                                             du_regrade'45'eff_5108 (coe v17) (coe v18) (coe v2)
                                             (coe v12) in
                                   coe
                                     (let v21
                                            = coe
                                                du_regrade'45'eff_5108 (coe v15) (coe v19) (coe v2)
                                                (coe v13) in
                                      coe
                                        (case coe v20 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v22
                                             -> case coe v21 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v23
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'case_544
                                                            v22 v23)
                                                  _ -> coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                           _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                              _ -> coe v4
                       _ -> coe v4
                _ -> coe v4
         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_596 v10
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_596 v10)
         _ -> coe v4)
-- Once.TypeCheck.Completeness.just≢nothing
d_just'8802'nothing_5190 ::
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_just'8802'nothing_5190 = erased
-- Once.TypeCheck.Completeness.StrongElab
d_StrongElab_5202 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 -> ()
d_StrongElab_5202 = erased
-- Once.TypeCheck.Completeness.go-canonical
d_go'45'canonical_5242 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go'45'canonical_5242 = erased
-- Once.TypeCheck.Completeness.composeGo-success
d_composeGo'45'success_5290 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
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
d_composeGo'45'success_5290 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 ~v9
                            ~v10 ~v11 ~v12 ~v13 ~v14 v15 v16 v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23
                            ~v24 ~v25
  = du_composeGo'45'success_5290 v6 v7 v8 v15 v16 v17
du_composeGo'45'success_5290 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_composeGo'45'success_5290 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.IR.C__'8728'__30
         (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v0)) v1 v2)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            addInt (coe (1 :: Integer))
            (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v3) (coe v5)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
            (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)))
-- Once.TypeCheck.Completeness.cgo-usage
d_cgo'45'usage_5356 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cgo'45'usage_5356 = erased
-- Once.TypeCheck.Completeness.ccgo-usage
d_ccgo'45'usage_5722 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ccgo'45'usage_5722 = erased
-- Once.TypeCheck.Completeness.ccatago-usage
d_ccatago'45'usage_6088 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ccatago'45'usage_6088 = erased
-- Once.TypeCheck.Completeness.named-morph-strong
d_named'45'morph'45'strong_6198
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.Completeness.named-morph-strong"
-- Once.TypeCheck.Completeness.named-morph-strong-resolved
d_named'45'morph'45'strong'45'resolved_6210
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.Completeness.named-morph-strong-resolved"
-- Once.TypeCheck.Completeness.checkG-realize
d_checkG'45'realize_6224 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_checkG'45'realize_6224 = erased
-- Once.TypeCheck.Completeness.morph-elab
d_morph'45'elab_6582 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_morph'45'elab_6582 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'id_456
        -> let v11
                 = coe
                     MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
                     (coe v0) (coe ("id" :: Data.Text.Text))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                        (coe ("id" :: Data.Text.Text))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v0)))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                        (coe ("id" :: Data.Text.Text))) in
           coe
             (case coe v11 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                  -> coe
                       seq (coe v12)
                       (let v14
                              = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                                  (coe ("id" :: Data.Text.Text))
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
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
                                        = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                               (coe v0))
                                            (coe ("id" :: Data.Text.Text)) in
                                  coe
                                    (case coe v15 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                         -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> let v16
                                                  = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
                                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'id_456)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                        (coe
                                                                           MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                                                           (coe
                                                                              MAlonzo.Code.Once.IR.C_id_22))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe (0 :: Integer))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                              (coe
                                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                                 (coe v0))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'id_456))
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'fst_466
        -> let v12
                 = coe
                     MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
                     (coe v0) (coe ("fst" :: Data.Text.Text))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                        (coe ("fst" :: Data.Text.Text))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v0)))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                        (coe ("fst" :: Data.Text.Text))) in
           coe
             (case coe v12 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                  -> coe
                       seq (coe v13)
                       (let v15
                              = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                                  (coe ("fst" :: Data.Text.Text))
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
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
                                        = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                               (coe v0))
                                            (coe ("fst" :: Data.Text.Text)) in
                                  coe
                                    (case coe v16 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                         -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> let v17
                                                  = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
                                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'fst_466)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                        (coe
                                                                           MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                                                           (coe
                                                                              MAlonzo.Code.Once.IR.C_fst_44))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe (0 :: Integer))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                              (coe
                                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                                 (coe v0))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'fst_466))
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'snd_476
        -> let v12
                 = coe
                     MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
                     (coe v0) (coe ("snd" :: Data.Text.Text))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                        (coe ("snd" :: Data.Text.Text))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v0)))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                        (coe ("snd" :: Data.Text.Text))) in
           coe
             (case coe v12 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                  -> coe
                       seq (coe v13)
                       (let v15
                              = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                                  (coe ("snd" :: Data.Text.Text))
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
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
                                        = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                               (coe v0))
                                            (coe ("snd" :: Data.Text.Text)) in
                                  coe
                                    (case coe v16 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                         -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> let v17
                                                  = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
                                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'snd_476)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                        (coe
                                                                           MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                                                           (coe
                                                                              MAlonzo.Code.Once.IR.C_snd_50))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe (0 :: Integer))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                              (coe
                                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                                 (coe v0))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'snd_476))
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'terminal_484
        -> let v11
                 = coe
                     MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
                     (coe v0) (coe ("terminal" :: Data.Text.Text))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                        (coe ("terminal" :: Data.Text.Text))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v0)))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                        (coe ("terminal" :: Data.Text.Text))) in
           coe
             (case coe v11 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                  -> coe
                       seq (coe v12)
                       (let v14
                              = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                                  (coe ("terminal" :: Data.Text.Text))
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
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
                                        = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
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
                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'terminal_484)
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe
                                                       MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                                       (coe MAlonzo.Code.Once.IR.C_terminal_74))
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe (0 :: Integer))
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                             (coe v0))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'terminal_484))
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'initial_492
        -> let v11
                 = coe
                     MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
                     (coe v0) (coe ("initial" :: Data.Text.Text))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                        (coe ("initial" :: Data.Text.Text))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v0)))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                        (coe ("initial" :: Data.Text.Text))) in
           coe
             (case coe v11 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                  -> coe
                       seq (coe v12)
                       (let v14
                              = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                                  (coe ("initial" :: Data.Text.Text))
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
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
                                        = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
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
                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'initial_492)
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe
                                                       MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                                       (coe MAlonzo.Code.Once.IR.C_initial_78))
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe (0 :: Integer))
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                             (coe v0))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'initial_492))
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inl_502
        -> let v12
                 = coe
                     MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
                     (coe v0) (coe ("inl" :: Data.Text.Text))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                        (coe ("inl" :: Data.Text.Text))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v0)))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                        (coe ("inl" :: Data.Text.Text))) in
           coe
             (case coe v12 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                  -> coe
                       seq (coe v13)
                       (let v15
                              = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                                  (coe ("inl" :: Data.Text.Text))
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
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
                                        = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                               (coe v0))
                                            (coe ("inl" :: Data.Text.Text)) in
                                  coe
                                    (case coe v16 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                         -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> let v17
                                                  = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
                                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inl_502)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                        (coe
                                                                           MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
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
                                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                                 (coe v0))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inl_502))
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inr_512
        -> let v12
                 = coe
                     MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
                     (coe v0) (coe ("inr" :: Data.Text.Text))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                        (coe ("inr" :: Data.Text.Text))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v0)))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                        (coe ("inr" :: Data.Text.Text))) in
           coe
             (case coe v12 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                  -> coe
                       seq (coe v13)
                       (let v15
                              = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                                  (coe ("inr" :: Data.Text.Text))
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
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
                                        = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                               (coe v0))
                                            (coe ("inr" :: Data.Text.Text)) in
                                  coe
                                    (case coe v16 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                         -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> let v17
                                                  = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__224
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
                                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inr_512)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                        (coe
                                                                           MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
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
                                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                                 (coe v0))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inr_512))
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'compose_528 v10 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
                      -> case coe v4 of
                           MAlonzo.Code.Once.Type.C_pure_34
                             -> let v20
                                      = d_morph'45'elab_6582
                                          (coe v0) (coe v19) (coe v10) (coe v3) (coe v4)
                                          (coe v14) in
                                coe
                                  (let v21
                                         = d_morph'45'elab_6582
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
                                                                                                                                                                 (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                                                                                                                                                                    (coe
                                                                                                                                                                       v10))
                                                                                                                                                                 v22
                                                                                                                                                                 v38)
                                                                                                                                                              (coe
                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                 (coe
                                                                                                                                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'compose_528
                                                                                                                                                                    v10
                                                                                                                                                                    v24
                                                                                                                                                                    v40)
                                                                                                                                                                 (coe
                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                    (coe
                                                                                                                                                                       MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                                                                                                                                                       (coe
                                                                                                                                                                          MAlonzo.Code.Once.IR.C__'8728'__30
                                                                                                                                                                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                                                                                                                                                                             (coe
                                                                                                                                                                                v10))
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
                                                                                                                                                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632
                                                                                                                                                                                (coe
                                                                                                                                                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'compose_528
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
                                      = d_morph'45'elab_6582
                                          (coe v0) (coe v19) (coe v10) (coe v3) (coe v4)
                                          (coe v14) in
                                coe
                                  (let v21
                                         = d_morph'45'elab_6582
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
                                                                                                                                                                 (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                                                                                                                                                                    (coe
                                                                                                                                                                       v10))
                                                                                                                                                                 v22
                                                                                                                                                                 v38)
                                                                                                                                                              (coe
                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                 (coe
                                                                                                                                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'compose_528
                                                                                                                                                                    v10
                                                                                                                                                                    v24
                                                                                                                                                                    v40)
                                                                                                                                                                 (coe
                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                    (coe
                                                                                                                                                                       MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                                                                                                                                                       (coe
                                                                                                                                                                          MAlonzo.Code.Once.IR.C__'8728'__30
                                                                                                                                                                          (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                                                                                                                                                                             (coe
                                                                                                                                                                                v10))
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
                                                                                                                                                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632
                                                                                                                                                                                (coe
                                                                                                                                                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'compose_528
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'case_544 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'43'__124 v19 v20
                             -> case coe v4 of
                                  MAlonzo.Code.Once.Type.C_pure_34
                                    -> let v21
                                             = d_morph'45'elab_6582
                                                 (coe v0) (coe v18) (coe v19) (coe v3) (coe v4)
                                                 (coe v13) in
                                       coe
                                         (let v22
                                                = d_morph'45'elab_6582
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
                                                                                                                                                                           MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'case_544
                                                                                                                                                                           v25
                                                                                                                                                                           v41)
                                                                                                                                                                        (coe
                                                                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                           (coe
                                                                                                                                                                              MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
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
                                                                                                                                                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632
                                                                                                                                                                                       (coe
                                                                                                                                                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'case_544
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
                                             = d_morph'45'elab_6582
                                                 (coe v0) (coe v18) (coe v19) (coe v3) (coe v4)
                                                 (coe v13) in
                                       coe
                                         (let v22
                                                = d_morph'45'elab_6582
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
                                                                                                                                                                           MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'case_544
                                                                                                                                                                           v25
                                                                                                                                                                           v41)
                                                                                                                                                                        (coe
                                                                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                           (coe
                                                                                                                                                                              MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
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
                                                                                                                                                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632
                                                                                                                                                                                       (coe
                                                                                                                                                                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'case_544
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'pair_558 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> case coe v14 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
                      -> case coe v3 of
                           MAlonzo.Code.Once.Type.C__'42'__122 v18 v19
                             -> let v20
                                      = d_morph'45'elab_6582
                                          (coe v0) (coe v17) (coe v2) (coe v18)
                                          (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v12) in
                                coe
                                  (let v21
                                         = d_morph'45'elab_6582
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
                                                                                                                                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'pair_558
                                                                                                                                                                    v24
                                                                                                                                                                    v40)
                                                                                                                                                                 (coe
                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                    (coe
                                                                                                                                                                       MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
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
                                                                                                                                                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632
                                                                                                                                                                                (coe
                                                                                                                                                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'pair_558
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'curry_570 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v14 v15 v16
                      -> let v17
                               = d_morph'45'elab_6582
                                   (coe v0) (coe v13)
                                   (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v2) (coe v14))
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
                                                                                            MAlonzo.Code.Once.IR.C_curry_86
                                                                                            v18
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.IR.C_Heap_8))
                                                                                         (coe
                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                            (coe
                                                                                               MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'curry_570
                                                                                               v20)
                                                                                            (coe
                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.IR.C_curry_86
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
                                                                                                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'curry_570
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'cata_584 v11 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_128 v16
                      -> coe
                           seq (coe v4)
                           (let v17
                                  = d_morph'45'elab_6582
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                            (coe v0))
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364
                                            (coe v0)))
                                      (coe v15)
                                      (coe
                                         MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v16)
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
                                                                                               MAlonzo.Code.Once.IR.C_Cata_106
                                                                                               (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                                                                                  (coe
                                                                                                     v16)
                                                                                                  (coe
                                                                                                     v11))
                                                                                               v18)
                                                                                            (coe
                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                               (coe
                                                                                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'cata_584
                                                                                                  v11
                                                                                                  v20)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.Surface.Syntax.C_cata_438
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
                                                                                                           MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                                                           (coe
                                                                                                              v0))
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'cata_584
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_596 v11
        -> coe
             du_const'45'morph'45'strong_6946 (coe v0) (coe v1) (coe v3)
             (coe v11)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named_608 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v16
               -> coe
                    d_named'45'morph'45'strong_6198 v0 v16 v2 v3 v4 erased erased
                    erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named'45'resolved_620 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v14
               -> coe
                    d_named'45'morph'45'strong'45'resolved_6210 v0 v14 v2 v3 v4 erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.morph-complete
d_morph'45'complete_6600 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_morph'45'complete_6600 v0 v1 v2 v3 v4 v5
  = let v6
          = d_morph'45'elab_6582
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
d_pair'45'eff'45'complete_6620 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pair'45'eff'45'complete_6620 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = d_morph'45'elab_6582
              (coe v0) (coe v1) (coe v3) (coe v4)
              (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v6) in
    coe
      (let v9
             = d_morph'45'elab_6582
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
                                                                                                                                     MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
                                                                                                                                     (coe
                                                                                                                                        MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
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
d_curry'45'eff'45'complete_6638 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_curry'45'eff'45'complete_6638 v0 v1 v2 v3 v4 v5
  = let v6
          = d_morph'45'elab_6582
              (coe v0) (coe v1)
              (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v2) (coe v3))
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
                                                                       MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
                                                                       (coe
                                                                          MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                                                          (coe
                                                                             MAlonzo.Code.Once.IR.C_curry_86
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
d_compose'45'eff'45'hlp_6670 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compose'45'eff'45'hlp_6670 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 ~v9
                             ~v10 ~v11 v12 ~v13
  = du_compose'45'eff'45'hlp_6670 v6 v7 v8 v12
du_compose'45'eff'45'hlp_6670 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compose'45'eff'45'hlp_6670 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_324 v6 v7 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) erased))
             MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_326 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Once.Surface.Syntax.C_arr''_376 v0)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) erased))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.compose-eff-complete
d_compose'45'eff'45'complete_6690 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_compose'45'eff'45'complete_6690 v0 v1 v2 v3 v4 v5 ~v6 v7 v8
  = du_compose'45'eff'45'complete_6690 v0 v1 v2 v3 v4 v5 v7 v8
du_compose'45'eff'45'complete_6690 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_compose'45'eff'45'complete_6690 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = d_morph'45'elab_6582
              (coe v0) (coe v1) (coe v4) (coe v5)
              (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v6) in
    coe
      (let v9
             = d_morph'45'elab_6582
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
                                                                                                                                  du_compose'45'eff'45'hlp_6670
                                                                                                                                  (coe
                                                                                                                                     MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                                                                                                                     (coe
                                                                                                                                        MAlonzo.Code.Once.IR.C__'8728'__30
                                                                                                                                        (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                                                                                                                                           (coe
                                                                                                                                              v4))
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
                                                                                                                                     MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkComposeGo_1954
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
d_case'45'eff'45'complete_6710 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_case'45'eff'45'complete_6710 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = d_morph'45'elab_6582
              (coe v0) (coe v1) (coe v3) (coe v5)
              (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v6) in
    coe
      (let v9
             = d_morph'45'elab_6582
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
                                                                                                                                             = coe
                                                                                                                                                 MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_2040
                                                                                                                                                 (coe
                                                                                                                                                    v0)
                                                                                                                                                 (coe
                                                                                                                                                    v1)
                                                                                                                                                 (coe
                                                                                                                                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
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
                                                                                                                                                   MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_324 v48 v49 v50 v51
                                                                                                                                                     -> let v52
                                                                                                                                                              = MAlonzo.Code.Once.TypeCheck.Elaborate.d_checkElabV_2032
                                                                                                                                                                  (coe
                                                                                                                                                                     v0)
                                                                                                                                                                  (coe
                                                                                                                                                                     v2)
                                                                                                                                                                  (coe
                                                                                                                                                                     MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
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
                                                                                                                                                                    MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_324 v55 v56 v57 v58
                                                                                                                                                                      -> let v59
                                                                                                                                                                               = coe
                                                                                                                                                                                   MAlonzo.Code.Once.TypeCheck.Elaborate.du_extract'45'morph'45'eff'45'aux_956
                                                                                                                                                                                   (coe
                                                                                                                                                                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
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
                                                                                                                                                                                      MAlonzo.Code.Once.TypeCheck.Elaborate.du_extract'45'morph'45'eff'45'aux_956
                                                                                                                                                                                      (coe
                                                                                                                                                                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
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
                                                                                                                                                                                         MAlonzo.Code.Once.TypeCheck.Judgment.du_extractMorphWitness_840
                                                                                                                                                                                         (coe
                                                                                                                                                                                            v1)
                                                                                                                                                                                         (coe
                                                                                                                                                                                            v47) in
                                                                                                                                                                               coe
                                                                                                                                                                                 (let v62
                                                                                                                                                                                        = coe
                                                                                                                                                                                            MAlonzo.Code.Once.TypeCheck.Judgment.du_extractMorphWitness_840
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
                                                                                                                                                                                                                                         MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
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
                                                                                                                                                                                                                                    MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
                                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                                       MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
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
                                                                                                                                                                                                                             MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
                                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                                MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
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
                                                                                                                                                                                                               MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
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
                                                                                                                                                                                                 MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
                                                                                                                                                                                                 (coe
                                                                                                                                                                                                    MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
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
                                                                                                                                                                    MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_326 v55
                                                                                                                                                                      -> coe
                                                                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                           (coe
                                                                                                                                                                              MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
                                                                                                                                                                              (coe
                                                                                                                                                                                 MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
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
                                                                                                                                                   MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_326 v48
                                                                                                                                                     -> coe
                                                                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                          (coe
                                                                                                                                                             MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
                                                                                                                                                             (coe
                                                                                                                                                                MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
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
d_cata'45'eff'45'complete_6728 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'eff'45'complete_6728 v0 v1 v2 v3 v4 ~v5 v6
  = du_cata'45'eff'45'complete_6728 v0 v1 v2 v3 v4 v6
du_cata'45'eff'45'complete_6728 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cata'45'eff'45'complete_6728 v0 v1 v2 v3 v4 v5
  = let v6
          = d_morph'45'elab_6582
              (coe
                 MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                 (coe MAlonzo.Code.Once.TypeCheck.Classify.d_polys_364 (coe v0)))
              (coe v1)
              (coe
                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v2) (coe v3))
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
                                                                            MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkCataGo_2010
                                                                            (coe v0) (coe v1)
                                                                            (coe v2) (coe v3)
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C_eff_36)
                                                                            (coe
                                                                               MAlonzo.Code.Once.Functor.Decide.d_wellFormedF'63'_224
                                                                               (coe v2)) in
                                                                  coe
                                                                    (case coe v23 of
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                                         -> case coe v24 of
                                                                              MAlonzo.Code.Once.TypeCheck.Elaborate.C_success_324 v26 v27 v28 v29
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
                                                                              MAlonzo.Code.Once.TypeCheck.Elaborate.C_failure_326 v26
                                                                                -> coe
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Surface.Syntax.C_arr''_376
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Surface.Syntax.C_cata_438
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
                                                                                              MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
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
d_check'45'completeV_6746 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_check'45'completeV_6746 v0 v1 v2 ~v3 v4
  = du_check'45'completeV_6746 v0 v1 v2 v4
du_check'45'completeV_6746 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_check'45'completeV_6746 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_2040
              (coe v0) (coe v1) (coe v2) in
    coe
      (let v5
             = coe
                 du_check'45'complete_6962 (coe v0) (coe v1) (coe v2) (coe v3) in
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
d_iFromInfer_6762 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_iFromInfer_6762 v0 v1 v2 ~v3 v4 = du_iFromInfer_6762 v0 v1 v2 v4
du_iFromInfer_6762 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_iFromInfer_6762 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_30
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v6
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.d_checkElab'45'fallback'45'RInt_16
                    (coe v0) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'float_42
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v9 v10 v11 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RFloat_52
                    (coe v0) (coe v9) (coe v10) (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'str_48
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_58 v6
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.d_checkElab'45'fallback'45'RStringLit_100
                    (coe v0) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_52
        -> coe
             MAlonzo.Code.Once.TypeCheck.ElaborateProofs.d_checkElab'45'fallback'45'RUnit_128
             (coe v0)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_56
        -> coe
             MAlonzo.Code.Once.TypeCheck.ElaborateProofs.d_checkElab'45'fallback'45'RVar'45'unit_1204
             (coe v0)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_68 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v11
               -> coe
                    du_checkElab'45'fallback'45'RVar_2696 (coe v0) (coe v11) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_78 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RQualified_164
                    (coe v0) (coe v10) (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_86 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v9
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RResolved_322
                    (coe v0) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_94 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v11
               -> coe
                    du_checkElab'45'fallback'45'RVar_2696 (coe v0) (coe v11) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_110 v7 v8 v9 v10 v18
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v19
               -> coe
                    du_checkElab'45'fallback'45'RVar_2696 (coe v0) (coe v19) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_120 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v9 v10
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RAnnot_466
                    (coe v0) (coe v9) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_136 v9 v10 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v13 v14
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__122 v15 v16
                      -> let v17
                               = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      du_iFromInfer_6762 (coe v0) (coe v13) (coe v15) (coe v11)) in
                         coe
                           (let v18
                                  = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            du_iFromInfer_6762 (coe v0) (coe v13) (coe v15)
                                            (coe v11))) in
                            coe
                              (coe
                                 du_pair'45'lit'45'reduce_6836 (coe v9) (coe v10) (coe v17)
                                 (coe v18)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe du_iFromInfer_6762 (coe v0) (coe v14) (coe v16) (coe v12)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          du_iFromInfer_6762 (coe v0) (coe v14) (coe v16)
                                          (coe v12))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             du_iFromInfer_6762 (coe v0) (coe v14) (coe v16)
                                             (coe v12)))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_144 v7
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v9
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RUnaryOp_996
                    (coe v0) (coe v9) (coe MAlonzo.Code.Once.Type.C_Int_132)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_156
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v10
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RUnaryOp_996
                    (coe v0) (coe v10) (coe MAlonzo.Code.Once.Type.C_Float_134)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_176 v8 v10 v11 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v15 v16 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RLet_614
                    (coe v0) (coe v15) (coe v16) (coe v17)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_206 v10 v11 v13 v14 v15 v16 v17 v18 v19 v20
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v21 v22 v23 v24 v25
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RDestruct_794
                    (coe v0) (coe v21) (coe v22) (coe v23) (coe v24) (coe v25)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_220 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RBinOp_5332
                    (coe v0) (coe v13) (coe v14) (coe v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_234 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RBinOp_5332
                    (coe v0) (coe v13) (coe v14) (coe v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_248 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RBinOp_5332
                    (coe v0) (coe v13) (coe v14) (coe v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_262 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RBinOp_5332
                    (coe v0) (coe v13) (coe v14) (coe v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_276 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v13 v14 v15
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RBinOp_5332
                    (coe v0) (coe v13) (coe v14) (coe v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_286 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'id_3968
                    (coe v0) (coe v10) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_298 v7 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'fst_4038
                    (coe v0) (coe v11) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_310 v6 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'snd_4108
                    (coe v0) (coe v11) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_320 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'terminal_5258
                    (coe v0) (coe v10) (coe MAlonzo.Code.Once.Type.C_Unit_118)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_332 v6 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'apply_2276
                    (coe v0) (coe v11) (coe v6) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_350 v7 v9 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'generic_4194
                    (coe v0) (coe v15) (coe v16) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_366 v7 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v16 v17 v18
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'generic_4194
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
-- Once.TypeCheck.Completeness.closed-lift-complete
d_closed'45'lift'45'complete_6780 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_ClosedLiftShape_100 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_closed'45'lift'45'complete_6780 v0 v1 ~v2 v3 v4 v5 ~v6
  = du_closed'45'lift'45'complete_6780 v0 v1 v3 v4 v5
du_closed'45'lift'45'complete_6780 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_ClosedLiftShape_100 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_closed'45'lift'45'complete_6780 v0 v1 v2 v3 v4
  = coe
      du_checkElab'45'closed'45'lift_4276 (coe v0) (coe v1) (coe v2)
      (coe v3) (coe v4)
-- Once.TypeCheck.Completeness.check-completeV-from-infer
d_check'45'completeV'45'from'45'infer_6798 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_check'45'completeV'45'from'45'infer_6798 v0 v1 v2 ~v3 v4
  = du_check'45'completeV'45'from'45'infer_6798 v0 v1 v2 v4
du_check'45'completeV'45'from'45'infer_6798 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_check'45'completeV'45'from'45'infer_6798 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkElabV'45'wf_2040
              (coe v0) (coe v1) (coe v2) in
    coe
      (let v5
             = coe du_iFromInfer_6762 (coe v0) (coe v1) (coe v2) (coe v3) in
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
d_pair'45'lit'45'reduce_6836 ::
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
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_pair'45'lit'45'reduce_6836 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 ~v9
                             ~v10 v11 v12 v13 ~v14 ~v15 ~v16
  = du_pair'45'lit'45'reduce_6836 v5 v6 v7 v8 v11 v12 v13
du_pair'45'lit'45'reduce_6836 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_pair'45'lit'45'reduce_6836 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.Surface.Syntax.C_pair_76 v0 v1 v2 v4)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v3) (coe v5))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) erased))
-- Once.TypeCheck.Completeness.iFromInferEff
d_iFromInferEff_6854 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_iFromInferEff_6854 v0 v1 v2 v3 ~v4 v5
  = du_iFromInferEff_6854 v0 v1 v2 v3 v5
du_iFromInferEff_6854 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_iFromInferEff_6854 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_68 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'eff_4754
                    (coe v0) (coe v12) (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_78 v10
        -> coe
             du_embedOrSubsume'45'lifts_3324 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024 (coe v0)
                (coe v1))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_86 v9
        -> coe
             du_embedOrSubsume'45'lifts_3324 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024 (coe v0)
                (coe v1))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_94 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'eff_4754
                    (coe v0) (coe v12) (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_110 v8 v9 v10 v11 v19
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v20
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'eff_4754
                    (coe v0) (coe v20) (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_120 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v10 v11
               -> coe
                    du_embedOrSubsume'45'lifts_3324 (coe v0)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 (coe v10)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v2)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v3)))
                    (coe v2) (coe v3)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024 (coe v0)
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_176 v9 v11 v12 v13 v14 v15
        -> coe
             du_embedOrSubsume'45'lifts_3324 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024 (coe v0)
                (coe v1))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_206 v11 v12 v14 v15 v16 v17 v18 v19 v20 v21
        -> coe
             du_embedOrSubsume'45'lifts_3324 (coe v0) (coe v1) (coe v2) (coe v3)
             (coe
                MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024 (coe v0)
                (coe v1))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_286 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'id'45'eff_4424
                    (coe v0) (coe v11) (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_298 v8 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'fst'45'eff_4534
                    (coe v0) (coe v12) (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_310 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'snd'45'eff_4644
                    (coe v0) (coe v12) (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_332 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'apply'45'eff_4906
                    (coe v0) (coe v12) (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_350 v8 v10 v11 v12 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'generic'45'eff_4282
                    (coe v0) (coe v16) (coe v17) (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.infer-complete
d_infer'45'complete_6870 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infer'45'complete_6870 v0 v1 v2 ~v3 v4
  = du_infer'45'complete_6870 v0 v1 v2 v4
du_infer'45'complete_6870 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infer'45'complete_6870 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_30
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v6
               -> coe d_infer'45'complete'45'RInt_16 (coe v0) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'float_42
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'str_48
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_58 v6
               -> coe d_infer'45'complete'45'RStringLit_30 (coe v0) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_52
        -> coe d_infer'45'complete'45'RUnit_42 (coe v0)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_56
        -> coe d_infer'45'complete'45'RVar'45'unit_52 (coe v0)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_68 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v11
               -> coe
                    du_infer'45'complete'45'RVar'45'local_856 (coe v0) (coe v11)
                    (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_78 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v10 v11
               -> coe
                    du_infer'45'complete'45'RQualified_68 (coe v0) (coe v10) (coe v11)
                    (coe v2) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_86 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v9
               -> coe
                    du_infer'45'complete'45'RResolved_212 (coe v0) (coe v9) (coe v2)
                    (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_94 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v11
               -> coe
                    du_infer'45'complete'45'RVar'45'import_930 (coe v0) (coe v11)
                    (coe v2) (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_110 v7 v8 v9 v10 v18
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v19
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'poly'45'infer_3926
                    (coe v0) (coe v19)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_120 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v9 v10
               -> coe
                    du_infer'45'complete'45'RAnnot_502 (coe v0) (coe v9) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_136 v9 v10 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v13 v14
               -> coe
                    du_infer'45'complete'45'RPair_374 (coe v0) (coe v13) (coe v14)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_144 v7
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v9
               -> coe
                    du_infer'45'complete'45'RUnaryOp'45'neg_432 (coe v0) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_156
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_176 v8 v10 v11 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v15 v16 v17
               -> coe
                    du_infer'45'complete'45'RLet_560 (coe v0) (coe v15) (coe v16)
                    (coe v17)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_206 v10 v11 v13 v14 v15 v16 v17 v18 v19 v20
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v21 v22 v23 v24 v25
               -> coe
                    du_infer'45'complete'45'RDestruct_2284 (coe v0) (coe v21) (coe v22)
                    (coe v23) (coe v24) (coe v25) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_220 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v13 v14 v15
               -> coe
                    du_infer'45'complete'45'RBinOp'45'arith_1594 (coe v0) (coe v13)
                    (coe v14) (coe v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_234 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v13 v14 v15
               -> coe
                    du_infer'45'complete'45'RBinOp'45'arith'45'float_1408 (coe v0)
                    (coe v13) (coe v14) (coe v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_248 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v13 v14 v15
               -> coe
                    du_infer'45'complete'45'RBinOp'45'arith'45'float'45'il_1036
                    (coe v0) (coe v13) (coe v14) (coe v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_262 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v13 v14 v15
               -> coe
                    du_infer'45'complete'45'RBinOp'45'arith'45'float'45'ir_1222
                    (coe v0) (coe v13) (coe v14) (coe v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_276 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v13 v14 v15
               -> coe
                    du_infer'45'complete'45'RBinOp'45'cmp_1818 (coe v0) (coe v13)
                    (coe v14) (coe v15)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_286 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> coe du_infer'45'complete'45'RApp'45'id_632 (coe v0) (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_298 v7 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe du_infer'45'complete'45'RApp'45'fst_710 (coe v0) (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_310 v6 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe du_infer'45'complete'45'RApp'45'snd_750 (coe v0) (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_320 v6 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> coe
                    du_infer'45'complete'45'RApp'45'terminal_670 (coe v0) (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_332 v6 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    du_infer'45'complete'45'RApp'45'apply_790 (coe v0) (coe v11)
                    (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_350 v7 v9 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> coe
                    du_infer'45'complete'45'RApp'45'generic_2482 (coe v0) (coe v15)
                    (coe v16) (coe v7) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_366 v7 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> coe
                    du_infer'45'complete'45'RApp'45'eff_2610 (coe v0) (coe v14)
                    (coe v15) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.nothing≢just
d_nothing'8802'just_6880 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  () -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_nothing'8802'just_6880 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_nothing'8802'just_6880
du_nothing'8802'just_6880 :: AgdaAny
du_nothing'8802'just_6880 = MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.checkG-just
d_checkG'45'just_6896 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_checkG'45'just_6896 v0 v1 v2 ~v3 v4
  = du_checkG'45'just_6896 v0 v1 v2 v4
du_checkG'45'just_6896 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_checkG'45'just_6896 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'int_372
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Once.Surface.Elaborate.du_intLit_8 (coe v6))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'int_372) erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'float_384
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v9 v10 v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Surface.Elaborate.du_floatLit_20
                       (coe
                          MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28 (coe v9) (coe v10)
                          (coe v11)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'float_384) erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'neg'45'int_390
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v7
               -> case coe v7 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.Surface.Elaborate.du_intLit_8
                              (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v8)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'neg'45'int_390)
                              erased)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'neg'45'float_402
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v10
               -> case coe v10 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v11 v12 v13 v14
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.Surface.Elaborate.du_floatLit_20
                              (coe
                                 MAlonzo.Code.Once.Float.Decimal.d_negate_22
                                 (coe
                                    MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28 (coe v11)
                                    (coe v12) (coe v13))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'neg'45'float_402)
                              erased)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'terminal_406
        -> let v7
                 = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                     (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                     (coe ("terminal" :: Data.Text.Text))
                     (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v0)) in
           coe
             (case coe v7 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                  -> case coe v8 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                         -> coe seq (coe v10) (coe du_nothing'8802'just_6880)
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> let v8
                           = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                               (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                               (coe ("terminal" :: Data.Text.Text)) in
                     coe
                       (case coe v8 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                            -> coe du_nothing'8802'just_6880
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe MAlonzo.Code.Once.IR.C_terminal_74)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'terminal_406)
                                    erased)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'pair_418 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__122 v13 v14
                      -> let v15
                               = coe
                                   du_checkG'45'just_6896 (coe v0) (coe v11) (coe v13) (coe v9) in
                         coe
                           (let v16
                                  = coe
                                      du_checkG'45'just_6896 (coe v0) (coe v12) (coe v14)
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
                                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'pair_418
                                                                   v19 v23)
                                                                erased)
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inl_428 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v11 v12
                      -> let v13
                               = coe
                                   du_checkG'45'just_6896 (coe v0) (coe v10) (coe v11) (coe v8) in
                         coe
                           (case coe v13 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                -> case coe v15 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               MAlonzo.Code.Once.IR.C__'8728'__30
                                               (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v11))
                                               (coe
                                                  MAlonzo.Code.Once.IR.C_inl_56
                                                  (coe MAlonzo.Code.Once.IR.C_Heap_8))
                                               v14)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inl_428
                                                  v16)
                                               erased)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inr_438 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v11 v12
                      -> let v13
                               = coe
                                   du_checkG'45'just_6896 (coe v0) (coe v10) (coe v12) (coe v8) in
                         coe
                           (case coe v13 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                -> case coe v15 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               MAlonzo.Code.Once.IR.C__'8728'__30
                                               (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v12))
                                               (coe
                                                  MAlonzo.Code.Once.IR.C_inr_62
                                                  (coe MAlonzo.Code.Once.IR.C_Heap_8))
                                               v14)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inr_438
                                                  v16)
                                               erased)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'In_448 v7 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_128 v12
                      -> let v13
                               = coe
                                   du_checkG'45'just_6896 (coe v0) (coe v11)
                                   (coe
                                      MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v12)
                                      (coe v2))
                                   (coe v9) in
                         coe
                           (let v14
                                  = MAlonzo.Code.Once.Functor.Decide.d_wellFormedF'63'_224
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
                                                         (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68
                                                            (coe
                                                               MAlonzo.Code.Once.IRTy.d_eraseF_40
                                                               (coe v12))
                                                            (coe
                                                               MAlonzo.Code.Once.IRTy.C_μ'45'type_26
                                                               (coe
                                                                  MAlonzo.Code.Once.IRTy.d_eraseF_40
                                                                  (coe v12))))
                                                         (coe
                                                            MAlonzo.Code.Once.IR.C_In_96
                                                            (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                                               (coe v12) (coe v15))
                                                            (coe MAlonzo.Code.Once.IR.C_Heap_8))
                                                         v16)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'In_448
                                                            v15 v18)
                                                         erased)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                   -> coe du_nothing'8802'just_6880
                                 _ -> MAlonzo.RTE.mazUnreachableError))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.gd-completeV
d_gd'45'completeV_6916 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_gd'45'completeV_6916 v0 v1 v2 ~v3 ~v4 v5
  = du_gd'45'completeV_6916 v0 v1 v2 v5
du_gd'45'completeV_6916 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_gd'45'completeV_6916 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'int_372
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                       (coe MAlonzo.Code.Once.Surface.Elaborate.du_intLit_8 (coe v6)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672
                                (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'int_372))
                             erased)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'float_384
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v9 v10 v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                       (coe
                          MAlonzo.Code.Once.Surface.Elaborate.du_floatLit_20
                          (coe
                             MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28 (coe v9) (coe v10)
                             (coe v11))))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672
                                (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'float_384))
                             erased)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'neg'45'int_390
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v7
               -> case coe v7 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                              (coe
                                 MAlonzo.Code.Once.Surface.Elaborate.du_intLit_8
                                 (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v8))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                    (coe v0))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'neg'45'int_390))
                                    erased)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'neg'45'float_402
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v10
               -> case coe v10 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v11 v12 v13 v14
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                              (coe
                                 MAlonzo.Code.Once.Surface.Elaborate.du_floatLit_20
                                 (coe
                                    MAlonzo.Code.Once.Float.Decimal.d_negate_22
                                    (coe
                                       MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28 (coe v11)
                                       (coe v12) (coe v13)))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                    (coe v0))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'neg'45'float_402))
                                    erased)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'terminal_406
        -> coe
             MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'terminalV_1822
             (coe v0)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'pair_418 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__122 v13 v14
                      -> let v15
                               = coe
                                   MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkG_1076 (coe v0)
                                   (coe v11) (coe v13) in
                         coe
                           (let v16
                                  = coe
                                      MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkG_1076 (coe v0)
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
                                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'pair_418
                                                                        v19 v22 in
                                                              coe
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe
                                                                      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                                                      v23)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe (0 :: Integer))
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                         (coe
                                                                            MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                            (coe v0))
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                            (coe
                                                                               MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672
                                                                               v24)
                                                                            erased)))))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> coe du_nothing'8802'just_6880
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> coe du_nothing'8802'just_6880))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inl_428 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v11 v12
                      -> let v13
                               = coe
                                   MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkG_1076 (coe v0)
                                   (coe v10) (coe v11) in
                         coe
                           (case coe v13 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                -> case coe v14 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                       -> let v17
                                                = coe
                                                    MAlonzo.Code.Once.IR.C__'8728'__30
                                                    (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                                                       (coe v11))
                                                    (coe
                                                       MAlonzo.Code.Once.IR.C_inl_56
                                                       (coe MAlonzo.Code.Once.IR.C_Heap_8))
                                                    v15 in
                                          coe
                                            (let v18
                                                   = coe
                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inl_428
                                                       v16 in
                                             coe
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                                     v17)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe (0 :: Integer))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe
                                                           MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                           (coe v0))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe
                                                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672
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
                                                      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                                      v15)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe (0 :: Integer))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                            (coe v0))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672
                                                               v16)
                                                            erased)))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                       -> coe du_nothing'8802'just_6880
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inr_438 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v11 v12
                      -> let v13
                               = coe
                                   MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkG_1076 (coe v0)
                                   (coe v10) (coe v12) in
                         coe
                           (case coe v13 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                -> case coe v14 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                       -> let v17
                                                = coe
                                                    MAlonzo.Code.Once.IR.C__'8728'__30
                                                    (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                                                       (coe v12))
                                                    (coe
                                                       MAlonzo.Code.Once.IR.C_inr_62
                                                       (coe MAlonzo.Code.Once.IR.C_Heap_8))
                                                    v15 in
                                          coe
                                            (let v18
                                                   = coe
                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inr_438
                                                       v16 in
                                             coe
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                                     v17)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe (0 :: Integer))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe
                                                           MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                           (coe v0))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe
                                                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672
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
                                                      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                                      v15)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe (0 :: Integer))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                            (coe v0))
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe
                                                               MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672
                                                               v16)
                                                            erased)))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                       -> coe du_nothing'8802'just_6880
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'In_448 v7 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_128 v12
                      -> let v13
                               = MAlonzo.Code.Once.Functor.Decide.d_wellFormedF'63'_224
                                   (coe v12) in
                         coe
                           (case coe v13 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                -> let v15
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkG_1076
                                             (coe v0) (coe v11)
                                             (coe
                                                MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                (coe v12) (coe v2)) in
                                   coe
                                     (case coe v15 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                          -> case coe v16 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                 -> let v19
                                                          = coe
                                                              MAlonzo.Code.Once.IR.C__'8728'__30
                                                              (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68
                                                                 (coe
                                                                    MAlonzo.Code.Once.IRTy.d_eraseF_40
                                                                    (coe v12))
                                                                 (coe
                                                                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26
                                                                    (coe
                                                                       MAlonzo.Code.Once.IRTy.d_eraseF_40
                                                                       (coe v12))))
                                                              (coe
                                                                 MAlonzo.Code.Once.IR.C_In_96
                                                                 (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                                                    (coe v12) (coe v14))
                                                                 (coe
                                                                    MAlonzo.Code.Once.IR.C_Heap_8))
                                                              v17 in
                                                    coe
                                                      (let v20
                                                             = coe
                                                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'In_448
                                                                 v14 v18 in
                                                       coe
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe
                                                               MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                                               v19)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe (0 :: Integer))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe
                                                                     MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                     (coe v0))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                     (coe
                                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672
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
                                                                MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                                                v17)
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe (0 :: Integer))
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe
                                                                      MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                      (coe v0))
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe
                                                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672
                                                                         v18)
                                                                      erased)))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                 -> let v16
                                                          = coe
                                                              du_checkG'45'just_6896 (coe v0)
                                                              (coe v11)
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                                 (coe v12) (coe v2))
                                                              (coe v9) in
                                                    coe
                                                      (case coe v16 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                           -> coe
                                                                seq (coe v18)
                                                                (coe du_nothing'8802'just_6880)
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                -> let v14 = coe du_nothing'8802'just_6880 in
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
d_gd'45'complete_6934 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_gd'45'complete_6934 v0 v1 v2 ~v3 ~v4 v5
  = du_gd'45'complete_6934 v0 v1 v2 v5
du_gd'45'complete_6934 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_gd'45'complete_6934 v0 v1 v2 v3
  = let v4
          = coe
              du_gd'45'completeV_6916 (coe v0) (coe v1) (coe v2) (coe v3) in
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
d_const'45'morph'45'strong_6946 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_const'45'morph'45'strong_6946 v0 v1 ~v2 v3 ~v4 v5
  = du_const'45'morph'45'strong_6946 v0 v1 v3 v5
du_const'45'morph'45'strong_6946 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_const'45'morph'45'strong_6946 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'int_372
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Once.Surface.Elaborate.du_intLit_8 (coe v6))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_596
                          (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'int_372))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                             (coe MAlonzo.Code.Once.Surface.Elaborate.du_intLit_8 (coe v6)))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                   (coe
                                      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672
                                      (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'int_372))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                            erased))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'float_384
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v9 v10 v11 v12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       MAlonzo.Code.Once.Surface.Elaborate.du_floatLit_20
                       (coe
                          MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28 (coe v9) (coe v10)
                          (coe v11)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_596
                          (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'float_384))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                             (coe
                                MAlonzo.Code.Once.Surface.Elaborate.du_floatLit_20
                                (coe
                                   MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28 (coe v9) (coe v10)
                                   (coe v11))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360 (coe v0))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                   (coe
                                      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672
                                      (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'float_384))
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                            erased))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'neg'45'int_390
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v7
               -> case coe v7 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.Surface.Elaborate.du_intLit_8
                              (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v8)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_596
                                 (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'neg'45'int_390))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                    (coe
                                       MAlonzo.Code.Once.Surface.Elaborate.du_intLit_8
                                       (coe MAlonzo.Code.Data.Integer.Base.d_'45'__260 (coe v8))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                          (coe v0))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'neg'45'int_390))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   erased erased))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'neg'45'float_402
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v10
               -> case coe v10 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v11 v12 v13 v14
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              MAlonzo.Code.Once.Surface.Elaborate.du_floatLit_20
                              (coe
                                 MAlonzo.Code.Once.Float.Decimal.d_negate_22
                                 (coe
                                    MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28 (coe v11)
                                    (coe v12) (coe v13))))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_596
                                 (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'neg'45'float_402))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                    (coe
                                       MAlonzo.Code.Once.Surface.Elaborate.du_floatLit_20
                                       (coe
                                          MAlonzo.Code.Once.Float.Decimal.d_negate_22
                                          (coe
                                             MAlonzo.Code.Once.Float.Decimal.d_decimalOf_28
                                             (coe v11) (coe v12) (coe v13)))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                          (coe v0))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672
                                             (coe
                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'neg'45'float_402))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   erased erased))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'terminal_406
        -> let v7
                 = coe
                     MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_2334
                     (coe v0) (coe ("terminal" :: Data.Text.Text))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                        (coe ("terminal" :: Data.Text.Text))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v0)))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                        (coe ("terminal" :: Data.Text.Text))) in
           coe
             (case coe v7 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                  -> coe
                       seq (coe v8)
                       (let v10
                              = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_484
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_354 (coe v0))
                                  (coe ("terminal" :: Data.Text.Text))
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_356 (coe v0))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358
                                     (coe v0)) in
                        coe
                          (case coe v10 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                               -> case coe v11 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                      -> coe seq (coe v13) (coe du_nothing'8802'just_6880)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                               -> let v11
                                        = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_442
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362
                                               (coe v0))
                                            (coe ("terminal" :: Data.Text.Text)) in
                                  coe
                                    (case coe v11 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                         -> coe du_nothing'8802'just_6880
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                              (coe MAlonzo.Code.Once.IR.C_terminal_74)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe
                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'terminal_484)
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe
                                                       MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                                       (coe MAlonzo.Code.Once.IR.C_terminal_74))
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe (0 :: Integer))
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                             (coe v0))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'terminal_484))
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
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'pair_418 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__122 v13 v14
                      -> let v15
                               = coe
                                   MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkG_1076 (coe v0)
                                   (coe v11) (coe v13) in
                         coe
                           (let v16
                                  = coe
                                      MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkG_1076 (coe v0)
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
                                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'pair_418
                                                                        v19 v22 in
                                                              coe
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe v23)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe
                                                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_596
                                                                         v24)
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                         (coe
                                                                            MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                                                            v23)
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                            (coe (0 :: Integer))
                                                                            (coe
                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                               (coe
                                                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                                  (coe v0))
                                                                               (coe
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672
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
                                               _ -> coe du_nothing'8802'just_6880
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> coe du_nothing'8802'just_6880))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inl_428 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v11 v12
                      -> let v13
                               = coe
                                   MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkG_1076 (coe v0)
                                   (coe v10) (coe v11) in
                         coe
                           (case coe v13 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                -> case coe v14 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                       -> let v17
                                                = coe
                                                    MAlonzo.Code.Once.IR.C__'8728'__30
                                                    (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                                                       (coe v11))
                                                    (coe
                                                       MAlonzo.Code.Once.IR.C_inl_56
                                                       (coe MAlonzo.Code.Once.IR.C_Heap_8))
                                                    v15 in
                                          coe
                                            (let v18
                                                   = coe
                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inl_428
                                                       v16 in
                                             coe
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v17)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_596
                                                        v18)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe
                                                           MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                                           v17)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe (0 :: Integer))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe
                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                 (coe v0))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe
                                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672
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
                                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_596
                                                         v16)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                                            v15)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe (0 :: Integer))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                  (coe v0))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe
                                                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672
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
                                       -> coe du_nothing'8802'just_6880
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inr_438 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v11 v12
                      -> let v13
                               = coe
                                   MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkG_1076 (coe v0)
                                   (coe v10) (coe v12) in
                         coe
                           (case coe v13 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                -> case coe v14 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                       -> let v17
                                                = coe
                                                    MAlonzo.Code.Once.IR.C__'8728'__30
                                                    (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                                                       (coe v12))
                                                    (coe
                                                       MAlonzo.Code.Once.IR.C_inr_62
                                                       (coe MAlonzo.Code.Once.IR.C_Heap_8))
                                                    v15 in
                                          coe
                                            (let v18
                                                   = coe
                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inr_438
                                                       v16 in
                                             coe
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v17)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_596
                                                        v18)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe
                                                           MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                                           v17)
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                           (coe (0 :: Integer))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              (coe
                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                 (coe v0))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe
                                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672
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
                                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_596
                                                         v16)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                                            v15)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe (0 :: Integer))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                  (coe v0))
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe
                                                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672
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
                                       -> coe du_nothing'8802'just_6880
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'In_448 v7 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_128 v12
                      -> let v13
                               = MAlonzo.Code.Once.Functor.Decide.d_wellFormedF'63'_224
                                   (coe v12) in
                         coe
                           (case coe v13 of
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                -> let v15
                                         = coe
                                             MAlonzo.Code.Once.TypeCheck.Elaborate.du_checkG_1076
                                             (coe v0) (coe v11)
                                             (coe
                                                MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                (coe v12) (coe v2)) in
                                   coe
                                     (case coe v15 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                          -> case coe v16 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                 -> let v19
                                                          = coe
                                                              MAlonzo.Code.Once.IR.C__'8728'__30
                                                              (MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68
                                                                 (coe
                                                                    MAlonzo.Code.Once.IRTy.d_eraseF_40
                                                                    (coe v12))
                                                                 (coe
                                                                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26
                                                                    (coe
                                                                       MAlonzo.Code.Once.IRTy.d_eraseF_40
                                                                       (coe v12))))
                                                              (coe
                                                                 MAlonzo.Code.Once.IR.C_In_96
                                                                 (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8970''8971'_46
                                                                    (coe v12) (coe v14))
                                                                 (coe
                                                                    MAlonzo.Code.Once.IR.C_Heap_8))
                                                              v17 in
                                                    coe
                                                      (let v20
                                                             = coe
                                                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'In_448
                                                                 v14 v18 in
                                                       coe
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe v19)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe
                                                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_596
                                                                  v20)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe
                                                                     MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                                                     v19)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                     (coe (0 :: Integer))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                        (coe
                                                                           MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                           (coe v0))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe
                                                                              MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672
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
                                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_596
                                                                   v18)
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe
                                                                      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414
                                                                      v17)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe (0 :: Integer))
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                         (coe
                                                                            MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_360
                                                                            (coe v0))
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                            (coe
                                                                               MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672
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
                                                              du_checkG'45'just_6896 (coe v0)
                                                              (coe v11)
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                                 (coe v12) (coe v2))
                                                              (coe v9) in
                                                    coe
                                                      (case coe v16 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                           -> coe
                                                                seq (coe v18)
                                                                (coe du_nothing'8802'just_6880)
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                -> let v14 = coe du_nothing'8802'just_6880 in
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
d_check'45'complete_6962 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_check'45'complete_6962 v0 v1 v2 ~v3 v4
  = du_check'45'complete_6962 v0 v1 v2 v4
du_check'45'complete_6962 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_check'45'complete_6962 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632 v9
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v10 v11 v12
               -> case coe v11 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v13 v14
                      -> coe
                           d_morph'45'complete_6600 (coe v0) (coe v1) (coe v10) (coe v12)
                           (coe v14) (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_642 v8
        -> coe du_iFromInfer_6762 (coe v0) (coe v1) (coe v2) (coe v8)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_660 v10 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v16 v17 v18
                      -> case coe v17 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v19 v20
                             -> coe
                                  du_check'45'complete'45'RLam_2084 (coe v0) (coe v14) (coe v15)
                                  (coe v16) (coe v19) (coe v10) (coe v18)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672 v9
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v10 v11 v12
               -> coe du_gd'45'complete_6934 (coe v0) (coe v1) (coe v12) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'closed'45'lift_684 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v11 v12 v13
               -> case coe v12 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v14 v15
                      -> coe
                           du_closed'45'lift'45'complete_6780 (coe v0) (coe v1) (coe v11)
                           (coe v15) (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_700 v9 v10 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v13 v14
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__122 v15 v16
                      -> let v17
                               = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      du_check'45'complete_6962 (coe v0) (coe v13) (coe v15)
                                      (coe v11)) in
                         coe
                           (let v18
                                  = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                         (coe
                                            du_check'45'complete_6962 (coe v0) (coe v13) (coe v15)
                                            (coe v11))) in
                            coe
                              (coe
                                 du_pair'45'lit'45'reduce_6836 (coe v9) (coe v10) (coe v17)
                                 (coe v18)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       du_check'45'complete_6962 (coe v0) (coe v14) (coe v16)
                                       (coe v12)))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          du_check'45'complete_6962 (coe v0) (coe v14) (coe v16)
                                          (coe v12))))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                          (coe
                                             du_check'45'complete_6962 (coe v0) (coe v14) (coe v16)
                                             (coe v12)))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_712 v7 v8 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_128 v13
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'In_2238
                           (coe v0) (coe v12) (coe v13) (coe v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_724 v6 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'apply_2276
                    (coe v0) (coe v11) (coe v6) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_736 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v12 v13
                      -> coe
                           du_completeness'45'gap'45'inl'45'app'45'check'45'eq_3068 (coe v0)
                           (coe v11) (coe v12)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_748 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v12 v13
                      -> coe
                           du_completeness'45'gap'45'inr'45'app'45'check'45'eq_3116 (coe v0)
                           (coe v11) (coe v13)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_758 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> coe
                    du_completeness'45'gap'45'initial'45'app'45'check'45'eq_3162
                    (coe v0) (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_770 v9
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v10 v11 v12
               -> coe
                    du_subsume'45'complete_6980 (coe v0) (coe v1) (coe v10) (coe v12)
                    (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_786 v7 v9 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> coe
                    d_completeness'45'gap'45'arg'45'driven'45'app'45'check_5072 v0 v14
                    v15 v7 v2 v9 v10 erased v12 v13
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_800 v7 v8 v9 v16
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v17
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'poly_3824
                    (coe v0) (coe v17)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Completeness.subsume-complete
d_subsume'45'complete_6980 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_subsume'45'complete_6980 v0 v1 v2 v3 ~v4 v5
  = du_subsume'45'complete_6980 v0 v1 v2 v3 v5
du_subsume'45'complete_6980 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_subsume'45'complete_6980 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_632 v10
        -> case coe v10 of
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'id_456
               -> coe
                    d_morph'45'complete_6600 (coe v0)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                       (coe ("id" :: Data.Text.Text)))
                    (coe v2) (coe v2) (coe MAlonzo.Code.Once.Type.C_eff_36)
                    (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'id_456)
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'fst_466
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__122 v17 v18
                      -> coe
                           d_morph'45'complete_6600 (coe v0)
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                              (coe ("fst" :: Data.Text.Text)))
                           (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v3) (coe v18))
                           (coe v3) (coe MAlonzo.Code.Once.Type.C_eff_36)
                           (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'fst_466)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'snd_476
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__122 v17 v18
                      -> coe
                           d_morph'45'complete_6600 (coe v0)
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                              (coe ("snd" :: Data.Text.Text)))
                           (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v17) (coe v3))
                           (coe v3) (coe MAlonzo.Code.Once.Type.C_eff_36)
                           (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'snd_476)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'terminal_484
               -> coe
                    d_morph'45'complete_6600 (coe v0)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                       (coe ("terminal" :: Data.Text.Text)))
                    (coe v2) (coe MAlonzo.Code.Once.Type.C_Unit_118)
                    (coe MAlonzo.Code.Once.Type.C_eff_36)
                    (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'terminal_484)
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'initial_492
               -> coe
                    d_morph'45'complete_6600 (coe v0)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                       (coe ("initial" :: Data.Text.Text)))
                    (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v3)
                    (coe MAlonzo.Code.Once.Type.C_eff_36)
                    (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'initial_492)
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inl_502
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v17 v18
                      -> coe
                           d_morph'45'complete_6600 (coe v0)
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                              (coe ("inl" :: Data.Text.Text)))
                           (coe v2)
                           (coe MAlonzo.Code.Once.Type.C__'43'__124 (coe v2) (coe v18))
                           (coe MAlonzo.Code.Once.Type.C_eff_36)
                           (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inl_502)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inr_512
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v17 v18
                      -> coe
                           d_morph'45'complete_6600 (coe v0)
                           (coe
                              MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                              (coe ("inr" :: Data.Text.Text)))
                           (coe v2)
                           (coe MAlonzo.Code.Once.Type.C__'43'__124 (coe v17) (coe v2))
                           (coe MAlonzo.Code.Once.Type.C_eff_36)
                           (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inr_512)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'compose_528 v15 v19 v20
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v21 v22
                      -> case coe v21 of
                           MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v23 v24
                             -> coe
                                  du_compose'45'eff'45'complete_6690 (coe v0) (coe v24) (coe v22)
                                  (coe v2) (coe v15) (coe v3) (coe v19) (coe v20)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'case_544 v18 v19
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v20 v21
                      -> case coe v20 of
                           MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v22 v23
                             -> case coe v2 of
                                  MAlonzo.Code.Once.Type.C__'43'__124 v24 v25
                                    -> coe
                                         d_case'45'eff'45'complete_6710 (coe v0) (coe v23) (coe v21)
                                         (coe v24) (coe v25) (coe v3) (coe v18) (coe v19)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'pair_558 v17 v18
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v19 v20
                      -> case coe v19 of
                           MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v21 v22
                             -> case coe v3 of
                                  MAlonzo.Code.Once.Type.C__'42'__122 v23 v24
                                    -> coe
                                         d_pair'45'eff'45'complete_6620 (coe v0) (coe v22) (coe v20)
                                         (coe v2) (coe v23) (coe v24) (coe v17) (coe v18)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'curry_570 v16
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
                      -> case coe v3 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v19 v20 v21
                             -> coe
                                  d_curry'45'eff'45'complete_6638 (coe v0) (coe v18) (coe v2)
                                  (coe v19) (coe v21) (coe v16)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'cata_584 v16 v18
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v19 v20
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C_μ'45'type_128 v21
                             -> coe
                                  du_cata'45'eff'45'complete_6728 (coe v0) (coe v20) (coe v21)
                                  (coe v3) (coe v16) (coe v18)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_596 v16
               -> coe
                    d_morph'45'complete_6600 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe MAlonzo.Code.Once.Type.C_eff_36)
                    (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_596 v16)
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named_608 v19 v20
               -> case coe v1 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v21
                      -> coe
                           MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'eff_4754
                           (coe v0) (coe v21) (coe v2) (coe v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named'45'resolved_620 v17 v18
               -> coe
                    du_embedOrSubsume'45'lifts_3324 (coe v0) (coe v1) (coe v2) (coe v3)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Elaborate.d_inferElabV_2024 (coe v0)
                       (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_642 v9
        -> coe
             du_iFromInferEff_6854 (coe v0) (coe v1) (coe v2) (coe v3) (coe v9)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_660 v11 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v15 v16
               -> coe
                    du_check'45'complete'45'RLam'45'eff_2174 (coe v0) (coe v15)
                    (coe v16) (coe v2) (coe v11) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_672 v10
        -> coe du_gd'45'complete_6934 (coe v0) (coe v1) (coe v3) (coe v10)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'closed'45'lift_684 v10 v11
        -> coe
             du_closed'45'lift'45'complete_6780 (coe v0) (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.Type.C_eff_36) (coe v10)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_724 v7 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    du_iFromInferEff_6854 (coe v0)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42
                       (coe
                          MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                          (coe ("apply" :: Data.Text.Text)))
                       (coe v12))
                    (coe v2) (coe v3)
                    (coe
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_332
                       v7 v9 v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_758 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RApp'45'initial'45'eff_4862
                    (coe v0) (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_786 v8 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> coe
                    d_completeness'45'gap'45'arg'45'driven'45'app'45'check'45'eff_5096
                    v0 v15 v16 v8 v2 v3 v10 v11 erased v13 v14
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_800 v8 v9 v10 v17
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v18
               -> coe
                    MAlonzo.Code.Once.TypeCheck.ElaborateProofs.du_checkElab'45'fallback'45'RVar'45'poly_3824
                    (coe v0) (coe v18)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
