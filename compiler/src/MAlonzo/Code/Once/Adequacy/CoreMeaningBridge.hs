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

module MAlonzo.Code.Once.Adequacy.CoreMeaningBridge where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.GradedOps
import qualified MAlonzo.Code.Once.Denotation.Meaning
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Spec.Contract
import qualified MAlonzo.Code.Once.Spec.Core.DerivedTyping
import qualified MAlonzo.Code.Once.Spec.Core.Meaning
import qualified MAlonzo.Code.Once.Spec.Core.PolyTy
import qualified MAlonzo.Code.Once.Spec.Core.Syntax
import qualified MAlonzo.Code.Once.Spec.Core.Typing
import qualified MAlonzo.Code.Once.Spec.Elaboration
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.Type.Sub
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.Adequacy.CoreMeaningBridge.GM.DefSem
d_DefSem_16 a0 a1 a2 a3 = ()
-- Once.Adequacy.CoreMeaningBridge.GM.⟦_⟧
d_'10214'_'10215'_30 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  AgdaAny -> AgdaAny
d_'10214'_'10215'_30 ~v0 v1 ~v2 ~v3 = du_'10214'_'10215'_30 v1
du_'10214'_'10215'_30 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  AgdaAny -> AgdaAny
du_'10214'_'10215'_30 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Spec.Core.Meaning.du_'10214'_'10215'_452 (coe v0)
      v2 v4 v5 v6 v7
-- Once.Adequacy.CoreMeaningBridge.GM.DefSem.defs
d_defs_34 ::
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196) ->
  AgdaAny
d_defs_34 v0
  = coe MAlonzo.Code.Once.Spec.Core.Meaning.d_defs_354 (coe v0)
-- Once.Adequacy.CoreMeaningBridge.GM.DefSem.impl
d_impl_36 ::
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_408
d_impl_36 v0
  = coe MAlonzo.Code.Once.Spec.Core.Meaning.d_impl_356 (coe v0)
-- Once.Adequacy.CoreMeaningBridge._.Elab
d_Elab_40 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_Elab_40 = erased
-- Once.Adequacy.CoreMeaningBridge._.ImportAt
d_ImportAt_42 a0 a1 a2 a3 a4 a5 = ()
-- Once.Adequacy.CoreMeaningBridge._.InstanceOf
d_InstanceOf_44 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_InstanceOf_44 = erased
-- Once.Adequacy.CoreMeaningBridge._.View
d_View_46 a0 a1 a2 a3 a4 a5 = ()
-- Once.Adequacy.CoreMeaningBridge._.Views
d_Views_50 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 -> ()
d_Views_50 = erased
-- Once.Adequacy.CoreMeaningBridge._.elabᵈ
d_elab'7496'_56 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_468 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elab'7496'_56 ~v0 v1 v2 v3 = du_elab'7496'_56 v1 v2 v3
du_elab'7496'_56 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_468 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_elab'7496'_56 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Elaboration.d_elab'7496'_754 (coe v0)
      (coe v1) (coe v2)
-- Once.Adequacy.CoreMeaningBridge._.elabᵢ
d_elab'7522'_58 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_468 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elab'7522'_58 ~v0 v1 v2 v3 = du_elab'7522'_58 v1 v2 v3
du_elab'7522'_58 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_468 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_elab'7522'_58 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Elaboration.d_elab'7522'_740 (coe v0)
      (coe v1) (coe v2)
-- Once.Adequacy.CoreMeaningBridge._.elabᶜ
d_elab'7580'_60 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_468 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elab'7580'_60 ~v0 v1 v2 v3 = du_elab'7580'_60 v1 v2 v3
du_elab'7580'_60 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_468 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_elab'7580'_60 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Elaboration.d_elab'7580'_730 (coe v0)
      (coe v1) (coe v2)
-- Once.Adequacy.CoreMeaningBridge._.subE
d_subE_66 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_subE_66 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_subE_66 v10
du_subE_66 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_subE_66 v0 = coe v0
-- Once.Adequacy.CoreMeaningBridge._.View.entry
d_entry_76 ::
  MAlonzo.Code.Once.Spec.Elaboration.T_View_468 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_entry_76 v0
  = coe MAlonzo.Code.Once.Spec.Elaboration.d_entry_532 (coe v0)
-- Once.Adequacy.CoreMeaningBridge._.View.ground
d_ground_78 ::
  MAlonzo.Code.Once.Spec.Elaboration.T_View_468 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ground_78 v0
  = coe MAlonzo.Code.Once.Spec.Elaboration.d_ground_546 (coe v0)
-- Once.Adequacy.CoreMeaningBridge._.View.imported
d_imported_80 ::
  MAlonzo.Code.Once.Spec.Elaboration.T_View_468 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_ImportAt_452
d_imported_80 v0
  = coe MAlonzo.Code.Once.Spec.Elaboration.d_imported_522 (coe v0)
-- Once.Adequacy.CoreMeaningBridge._.View.inst
d_inst_82 ::
  MAlonzo.Code.Once.Spec.Elaboration.T_View_468 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inst_82 v0
  = coe MAlonzo.Code.Once.Spec.Elaboration.d_inst_560 (coe v0)
-- Once.Adequacy.CoreMeaningBridge.refSem
d_refSem_90 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_refSem_90 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7 = du_refSem_90 v4 v5 v7
du_refSem_90 ::
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_refSem_90 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe MAlonzo.Code.Once.Spec.Core.Meaning.d_defs_354 v0 v1 v3 v5
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoreMeaningBridge.impSem
d_impSem_110 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_ImportAt_452 -> AgdaAny
d_impSem_110 v0 v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_impSem_110 v0 v1 v4 v5 v6 v7 v8
du_impSem_110 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_ImportAt_452 -> AgdaAny
du_impSem_110 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.Spec.Elaboration.C_ffi_458 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.Denotation.GradedOps.du_sigOpRef'7515'_514
             (coe v3) (coe v0) (coe v1)
             (coe MAlonzo.Code.Once.Spec.Core.Meaning.d_impl_356 (coe v2))
             (coe v4) (coe v5)
      MAlonzo.Code.Once.Spec.Elaboration.C_def_462 v7 v8
        -> coe du_refSem_90 (coe v2) (coe v7) (coe v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoreMeaningBridge.Agree
d_Agree_140 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_Agree_140 = C_constructor_288
-- Once.Adequacy.CoreMeaningBridge.Agree.agree-inst
d_agree'45'inst_236 ::
  T_Agree_140 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'inst_236 = erased
-- Once.Adequacy.CoreMeaningBridge.Agree.agree-ground
d_agree'45'ground_250 ::
  T_Agree_140 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'ground_250 = erased
-- Once.Adequacy.CoreMeaningBridge.Agree.agree-import
d_agree'45'import_260 ::
  T_Agree_140 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'import_260 = erased
-- Once.Adequacy.CoreMeaningBridge.Agree.agree-qualified
d_agree'45'qualified_272 ::
  T_Agree_140 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'qualified_272 = erased
-- Once.Adequacy.CoreMeaningBridge.Agree.agree-resolved
d_agree'45'resolved_284 ::
  T_Agree_140 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_222 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'resolved_284 = erased
-- Once.Adequacy.CoreMeaningBridge.Agree.agree-world
d_agree'45'world_286 ::
  T_Agree_140 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'world_286 = erased
-- Once.Adequacy.CoreMeaningBridge._.Tm
d_Tm_302 a0 a1 a2 a3 a4 = ()
-- Once.Adequacy.CoreMeaningBridge._._⊢[_]_∷_!_
d__'8866''91'_'93'_'8759'_'33'__520 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
  = ()
-- Once.Adequacy.CoreMeaningBridge._.⊢anaᶜ
d_'8866'ana'7580'_626 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'ana'7580'_626 ~v0 ~v1 ~v2 ~v3 = du_'8866'ana'7580'_626
du_'8866'ana'7580'_626 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'ana'7580'_626
  = coe
      MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'ana'7580'_760
-- Once.Adequacy.CoreMeaningBridge._.⊢applyEffᶜ
d_'8866'applyEff'7580'_628 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'applyEff'7580'_628 ~v0 ~v1 ~v2 ~v3
  = du_'8866'applyEff'7580'_628
du_'8866'applyEff'7580'_628 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'applyEff'7580'_628 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'applyEff'7580'_818
      v0 v2 v3
-- Once.Adequacy.CoreMeaningBridge._.⊢applyᶜ
d_'8866'apply'7580'_630 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'apply'7580'_630 ~v0 ~v1 ~v2 ~v3 = du_'8866'apply'7580'_630
du_'8866'apply'7580'_630 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'apply'7580'_630 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'apply'7580'_784
      v0 v2 v3
-- Once.Adequacy.CoreMeaningBridge._.⊢caseᶜ
d_'8866'case'7580'_632 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'case'7580'_632 ~v0 ~v1 ~v2 ~v3 = du_'8866'case'7580'_632
du_'8866'case'7580'_632 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'case'7580'_632 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'case'7580'_660
      v0 v1 v2 v3 v4 v5 v6 v7 v9 v10 v11
-- Once.Adequacy.CoreMeaningBridge._.⊢cataᶜ
d_'8866'cata'7580'_634 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'cata'7580'_634 ~v0 ~v1 ~v2 ~v3 = du_'8866'cata'7580'_634
du_'8866'cata'7580'_634 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'cata'7580'_634 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'cata'7580'_730
      v0 v2 v3 v4 v5 v7 v8
-- Once.Adequacy.CoreMeaningBridge._.⊢composeᶜ
d_'8866'compose'7580'_636 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'compose'7580'_636 ~v0 ~v1 ~v2 ~v3
  = du_'8866'compose'7580'_636
du_'8866'compose'7580'_636 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'compose'7580'_636 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'compose'7580'_576
      v0 v1 v2 v3 v4 v5 v6 v7 v9 v10 v11
-- Once.Adequacy.CoreMeaningBridge._.⊢curryᶜ
d_'8866'curry'7580'_638 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'curry'7580'_638 ~v0 ~v1 ~v2 ~v3 = du_'8866'curry'7580'_638
du_'8866'curry'7580'_638 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'curry'7580'_638 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'curry'7580'_698
      v0 v2 v3 v4 v5 v6 v7 v9
-- Once.Adequacy.CoreMeaningBridge._.⊢effAppᶜ
d_'8866'effApp'7580'_640 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'effApp'7580'_640 ~v0 ~v1 ~v2 ~v3
  = du_'8866'effApp'7580'_640
du_'8866'effApp'7580'_640 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'effApp'7580'_640 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'effApp'7580'_850
      v1 v2 v3 v4 v5 v6 v7 v8 v9
-- Once.Adequacy.CoreMeaningBridge._.⊢pairᶜ
d_'8866'pair'7580'_658 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'pair'7580'_658 ~v0 ~v1 ~v2 ~v3 = du_'8866'pair'7580'_658
du_'8866'pair'7580'_658 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'pair'7580'_658 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'pair'7580'_622
      v0 v1 v2 v3 v4 v5 v6 v7 v9 v10 v11
-- Once.Adequacy.CoreMeaningBridge.env-subst
d_env'45'subst_754 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'subst_754 = erased
-- Once.Adequacy.CoreMeaningBridge.drop-bind
d_drop'45'bind_792 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'bind_792 = erased
-- Once.Adequacy.CoreMeaningBridge.env-subst₂
d_env'45'subst'8322'_832 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Surface.Context.T__'8849''7512'__276 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'subst'8322'_832 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.bindC
d_bindC_862 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bindC_862 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.compose-sem
d_compose'45'sem_902 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compose'45'sem_902 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb._.E
d_E_922 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_E_922 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.pair-sem
d_pair'45'sem_978 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pair'45'sem_978 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb._.E
d_E_998 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_E_998 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.case-arm
d_case'45'arm_1042 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_case'45'arm_1042 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.case-sem
d_case'45'sem_1092 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_case'45'sem_1092 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb._.E
d_E_1118 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_E_1118 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.curry-sem
d_curry'45'sem_1158 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_curry'45'sem_1158 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb._.E
d_E_1176 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_E_1176 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb._._∙_
d__'8729'__1182 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d__'8729'__1182 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.appC-sem
d_appC'45'sem_1220 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_appC'45'sem_1220 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.bind2β
d_bind2β_1262 ::
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  () ->
  () ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bind2β_1262 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.apply-sem
d_apply'45'sem_1296 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'sem_1296 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.substΨ1
d_substΨ1_1334 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_substΨ1_1334 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.ana-sem″
d_ana'45'sem'8243'_1366 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ana'45'sem'8243'_1366 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.applyEff-sem
d_applyEff'45'sem_1402 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_applyEff'45'sem_1402 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.effApp-sem
d_effApp'45'sem_1436 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_effApp'45'sem_1436 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.cata-sem′
d_cata'45'sem'8242'_1476 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cata'45'sem'8242'_1476 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb._.E
d_E_1494 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_E_1494 = erased
-- Once.Adequacy.CoreMeaningBridge.assocT
d_assocT_1514 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assocT_1514 = erased
-- Once.Adequacy.CoreMeaningBridge.idʳT
d_id'691'T_1526 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  () ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_id'691'T_1526 = erased
-- Once.Adequacy.CoreMeaningBridge.subE-sem
d_subE'45'sem_1548 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subE'45'sem_1548 = erased
-- Once.Adequacy.CoreMeaningBridge.refSem-⊢
d_refSem'45''8866'_1570 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refSem'45''8866'_1570 = erased
-- Once.Adequacy.CoreMeaningBridge._.bindC
d_bindC_1604 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bindC_1604 = erased
-- Once.Adequacy.CoreMeaningBridge._.app-comb
d_app'45'comb_1630 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_app'45'comb_1630 = erased
-- Once.Adequacy.CoreMeaningBridge._.binK
d_binK_1662 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  () ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_binK_1662 = erased
-- Once.Adequacy.CoreMeaningBridge._.bridge-d
d_bridge'45'd_1696 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_468 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_302 ->
  T_Agree_140 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge'45'd_1696 = erased
-- Once.Adequacy.CoreMeaningBridge._.bridge-i
d_bridge'45'i_1716 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_468 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_302 ->
  T_Agree_140 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge'45'i_1716 = erased
-- Once.Adequacy.CoreMeaningBridge._.bridge-c
d_bridge'45'c_1736 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_468 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_302 ->
  T_Agree_140 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge'45'c_1736 = erased
-- Once.Adequacy.CoreMeaningBridge._..extendedlambda0
d_'46'extendedlambda0_2538 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_340 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_468 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_302 ->
  T_Agree_140 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'46'extendedlambda0_2538 = erased
