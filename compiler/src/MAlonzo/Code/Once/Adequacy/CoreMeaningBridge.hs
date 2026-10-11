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
import qualified MAlonzo.Code.Once.Denotation.Meaning
import qualified MAlonzo.Code.Once.Denotation.PhaseV
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Contract
import qualified MAlonzo.Code.Once.Spec.Core.DerivedTyping
import qualified MAlonzo.Code.Once.Spec.Core.Meaning
import qualified MAlonzo.Code.Once.Spec.Core.PolyTy
import qualified MAlonzo.Code.Once.Spec.Core.Syntax
import qualified MAlonzo.Code.Once.Spec.Core.Typing
import qualified MAlonzo.Code.Once.Spec.Elaboration
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Syntax
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Spec.Type.Grade
import qualified MAlonzo.Code.Once.Spec.Type.Poly
import qualified MAlonzo.Code.Once.Spec.Type.Sub
import qualified MAlonzo.Code.Once.Spec.Type.WellFormed
import qualified MAlonzo.Code.Once.Spec.Typing
import qualified MAlonzo.Code.Once.Spec.Typing.Scope
import qualified MAlonzo.Code.Once.Target.Arch

-- Once.Adequacy.CoreMeaningBridge.GM.DefSem
d_DefSem_16 a0 a1 a2 a3 = ()
-- Once.Adequacy.CoreMeaningBridge.GM.⟦_⟧
d_'10214'_'10215'_30 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  AgdaAny -> AgdaAny
d_'10214'_'10215'_30 ~v0 v1 ~v2 ~v3 = du_'10214'_'10215'_30 v1
du_'10214'_'10215'_30 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  AgdaAny -> AgdaAny
du_'10214'_'10215'_30 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Spec.Core.Meaning.du_'10214'_'10215'_460 (coe v0)
      v2 v3 v4 v5 v6 v7
-- Once.Adequacy.CoreMeaningBridge.GM.DefSem.defs
d_defs_34 ::
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  AgdaAny
d_defs_34 v0
  = coe MAlonzo.Code.Once.Spec.Core.Meaning.d_defs_362 (coe v0)
-- Once.Adequacy.CoreMeaningBridge.GM.DefSem.impl
d_impl_36 ::
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  MAlonzo.Code.Once.Spec.Contract.T_Impl_292
d_impl_36 v0
  = coe MAlonzo.Code.Once.Spec.Core.Meaning.d_impl_364 (coe v0)
-- Once.Adequacy.CoreMeaningBridge._.Elab
d_Elab_44 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 -> ()
d_Elab_44 = erased
-- Once.Adequacy.CoreMeaningBridge._.ImportAt
d_ImportAt_46 a0 a1 a2 a3 a4 a5 = ()
-- Once.Adequacy.CoreMeaningBridge._.InstanceOf
d_InstanceOf_50 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 -> ()
d_InstanceOf_50 = erased
-- Once.Adequacy.CoreMeaningBridge._.View
d_View_52 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.Adequacy.CoreMeaningBridge._.Views
d_Views_56 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 -> ()
d_Views_56 = erased
-- Once.Adequacy.CoreMeaningBridge._.elabᵈ
d_elab'7496'_60 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elab'7496'_60 ~v0 v1 v2 v3 = du_elab'7496'_60 v1 v2 v3
du_elab'7496'_60 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_elab'7496'_60 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Elaboration.d_elab'7496'_800 (coe v0)
      (coe v1) (coe v2)
-- Once.Adequacy.CoreMeaningBridge._.elabᵢ
d_elab'7522'_62 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elab'7522'_62 ~v0 v1 v2 v3 = du_elab'7522'_62 v1 v2 v3
du_elab'7522'_62 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_elab'7522'_62 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Elaboration.d_elab'7522'_786 (coe v0)
      (coe v1) (coe v2)
-- Once.Adequacy.CoreMeaningBridge._.elabᶜ
d_elab'7580'_64 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elab'7580'_64 ~v0 v1 v2 v3 = du_elab'7580'_64 v1 v2 v3
du_elab'7580'_64 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_elab'7580'_64 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Elaboration.d_elab'7580'_776 (coe v0)
      (coe v1) (coe v2)
-- Once.Adequacy.CoreMeaningBridge._.subE
d_subE_66 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_subE_66 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_subE_66 v10
du_subE_66 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_subE_66 v0 = coe v0
-- Once.Adequacy.CoreMeaningBridge._.ImportAt.entryOf
d_entryOf_78 ::
  MAlonzo.Code.Once.Spec.Elaboration.T_ImportAt_478 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_entryOf_78 v0
  = coe MAlonzo.Code.Once.Spec.Elaboration.d_entryOf_488 (coe v0)
-- Once.Adequacy.CoreMeaningBridge._.ImportAt.instOf
d_instOf_80 ::
  MAlonzo.Code.Once.Spec.Elaboration.T_ImportAt_478 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_instOf_80 v0
  = coe MAlonzo.Code.Once.Spec.Elaboration.d_instOf_490 (coe v0)
-- Once.Adequacy.CoreMeaningBridge._.View.declares
d_declares_84 ::
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_Declared_454
d_declares_84 v0
  = coe MAlonzo.Code.Once.Spec.Elaboration.d_declares_568 (coe v0)
-- Once.Adequacy.CoreMeaningBridge._.View.entry
d_entry_86 ::
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_entry_86 v0
  = coe MAlonzo.Code.Once.Spec.Elaboration.d_entry_578 (coe v0)
-- Once.Adequacy.CoreMeaningBridge._.View.ground
d_ground_88 ::
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ground_88 v0
  = coe MAlonzo.Code.Once.Spec.Elaboration.d_ground_592 (coe v0)
-- Once.Adequacy.CoreMeaningBridge._.View.imported
d_imported_90 ::
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_ImportAt_478
d_imported_90 v0
  = coe MAlonzo.Code.Once.Spec.Elaboration.d_imported_562 (coe v0)
-- Once.Adequacy.CoreMeaningBridge._.View.inst
d_inst_92 ::
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inst_92 v0
  = coe MAlonzo.Code.Once.Spec.Elaboration.d_inst_606 (coe v0)
-- Once.Adequacy.CoreMeaningBridge.refSem
d_refSem_100 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_refSem_100 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7 = du_refSem_100 v4 v5 v7
du_refSem_100 ::
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_refSem_100 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe MAlonzo.Code.Once.Spec.Core.Meaning.d_defs_362 v0 v1 v3 v5
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoreMeaningBridge.impSem
d_impSem_120 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_ImportAt_478 -> AgdaAny
d_impSem_120 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 = du_impSem_120 v4 v7
du_impSem_120 ::
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_ImportAt_478 -> AgdaAny
du_impSem_120 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Elaboration.C_def_492 v2 v3
        -> coe du_refSem_100 (coe v0) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoreMeaningBridge.Agree
d_Agree_140 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_Agree_140 = C_constructor_282
-- Once.Adequacy.CoreMeaningBridge.Agree.agree-inst
d_agree'45'inst_234 ::
  T_Agree_140 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'inst_234 = erased
-- Once.Adequacy.CoreMeaningBridge.Agree.agree-ground
d_agree'45'ground_248 ::
  T_Agree_140 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'ground_248 = erased
-- Once.Adequacy.CoreMeaningBridge.Agree.agree-import
d_agree'45'import_256 ::
  T_Agree_140 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'import_256 = erased
-- Once.Adequacy.CoreMeaningBridge.Agree.agree-qualified
d_agree'45'qualified_268 ::
  T_Agree_140 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'qualified_268 = erased
-- Once.Adequacy.CoreMeaningBridge.Agree.agree-resolved
d_agree'45'resolved_278 ::
  T_Agree_140 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'resolved_278 = erased
-- Once.Adequacy.CoreMeaningBridge.Agree.agree-world
d_agree'45'world_280 ::
  T_Agree_140 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'world_280 = erased
-- Once.Adequacy.CoreMeaningBridge._.Tm
d_Tm_296 a0 a1 a2 a3 a4 = ()
-- Once.Adequacy.CoreMeaningBridge._._⊢[_]_∷_!_
d__'8866''91'_'93'_'8759'_'33'__514 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
  = ()
-- Once.Adequacy.CoreMeaningBridge._.⊢anaᶜ
d_'8866'ana'7580'_628 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'ana'7580'_628 ~v0 ~v1 ~v2 ~v3 = du_'8866'ana'7580'_628
du_'8866'ana'7580'_628 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'ana'7580'_628
  = coe
      MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'ana'7580'_768
-- Once.Adequacy.CoreMeaningBridge._.⊢applyEffᶜ
d_'8866'applyEff'7580'_630 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'applyEff'7580'_630 ~v0 ~v1 ~v2 ~v3
  = du_'8866'applyEff'7580'_630
du_'8866'applyEff'7580'_630 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'applyEff'7580'_630 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'applyEff'7580'_826
      v0 v2 v3
-- Once.Adequacy.CoreMeaningBridge._.⊢applyᶜ
d_'8866'apply'7580'_632 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'apply'7580'_632 ~v0 ~v1 ~v2 ~v3 = du_'8866'apply'7580'_632
du_'8866'apply'7580'_632 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'apply'7580'_632 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'apply'7580'_792
      v0 v2 v3
-- Once.Adequacy.CoreMeaningBridge._.⊢caseᶜ
d_'8866'case'7580'_634 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'case'7580'_634 ~v0 ~v1 ~v2 ~v3 = du_'8866'case'7580'_634
du_'8866'case'7580'_634 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'case'7580'_634 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'case'7580'_664
      v0 v1 v2 v3 v4 v5 v6 v7 v9 v10 v11
-- Once.Adequacy.CoreMeaningBridge._.⊢cataᶜ
d_'8866'cata'7580'_636 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'cata'7580'_636 ~v0 ~v1 ~v2 ~v3 = du_'8866'cata'7580'_636
du_'8866'cata'7580'_636 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'cata'7580'_636 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'cata'7580'_734
      v0 v2 v3 v4 v5 v7 v8
-- Once.Adequacy.CoreMeaningBridge._.⊢composeᶜ
d_'8866'compose'7580'_638 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'compose'7580'_638 ~v0 ~v1 ~v2 ~v3
  = du_'8866'compose'7580'_638
du_'8866'compose'7580'_638 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'compose'7580'_638 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'compose'7580'_580
      v0 v1 v2 v3 v4 v5 v6 v7 v9 v10 v11
-- Once.Adequacy.CoreMeaningBridge._.⊢curryᶜ
d_'8866'curry'7580'_640 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'curry'7580'_640 ~v0 ~v1 ~v2 ~v3 = du_'8866'curry'7580'_640
du_'8866'curry'7580'_640 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'curry'7580'_640 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'curry'7580'_702
      v0 v2 v3 v4 v5 v6 v7 v9
-- Once.Adequacy.CoreMeaningBridge._.⊢effAppᶜ
d_'8866'effApp'7580'_642 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'effApp'7580'_642 ~v0 ~v1 ~v2 ~v3
  = du_'8866'effApp'7580'_642
du_'8866'effApp'7580'_642 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'effApp'7580'_642 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'effApp'7580'_858
      v1 v2 v3 v4 v5 v6 v7 v8 v9
-- Once.Adequacy.CoreMeaningBridge._.⊢pairᶜ
d_'8866'pair'7580'_660 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'pair'7580'_660 ~v0 ~v1 ~v2 ~v3 = du_'8866'pair'7580'_660
du_'8866'pair'7580'_660 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'pair'7580'_660 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'pair'7580'_626
      v0 v1 v2 v3 v4 v5 v6 v7 v9 v10 v11
-- Once.Adequacy.CoreMeaningBridge.env-subst
d_env'45'subst_732 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'subst_732 = erased
-- Once.Adequacy.CoreMeaningBridge.drop-bind
d_drop'45'bind_770 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'bind_770 = erased
-- Once.Adequacy.CoreMeaningBridge.env-subst₂
d_env'45'subst'8322'_810 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'subst'8322'_810 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.bindC
d_bindC_840 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bindC_840 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.compose-sem
d_compose'45'sem_880 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compose'45'sem_880 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb._.E
d_E_900 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_E_900 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.pair-sem
d_pair'45'sem_956 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pair'45'sem_956 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb._.E
d_E_976 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_E_976 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.case-arm
d_case'45'arm_1020 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_case'45'arm_1020 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.case-sem
d_case'45'sem_1070 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_case'45'sem_1070 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb._.E
d_E_1096 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_E_1096 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.curry-sem
d_curry'45'sem_1136 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_curry'45'sem_1136 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb._.E
d_E_1154 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_E_1154 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb._._∙_
d__'8729'__1160 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
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
d__'8729'__1160 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.appC-sem
d_appC'45'sem_1198 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_appC'45'sem_1198 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.bind2β
d_bind2β_1240 ::
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
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
d_bind2β_1240 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.apply-sem
d_apply'45'sem_1274 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'sem_1274 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.substΨ1
d_substΨ1_1312 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_substΨ1_1312 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.ana-sem″
d_ana'45'sem'8243'_1344 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ana'45'sem'8243'_1344 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.applyEff-sem
d_applyEff'45'sem_1380 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_applyEff'45'sem_1380 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.effApp-sem
d_effApp'45'sem_1414 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_effApp'45'sem_1414 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.cata-sem′
d_cata'45'sem'8242'_1454 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cata'45'sem'8242'_1454 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb._.E
d_E_1472 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_E_1472 = erased
-- Once.Adequacy.CoreMeaningBridge.assocT
d_assocT_1496 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assocT_1496 = erased
-- Once.Adequacy.CoreMeaningBridge.idʳT
d_id'691'T_1508 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  () ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_id'691'T_1508 = erased
-- Once.Adequacy.CoreMeaningBridge.subE-sem
d_subE'45'sem_1530 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subE'45'sem_1530 = erased
-- Once.Adequacy.CoreMeaningBridge.refSem-⊢
d_refSem'45''8866'_1552 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refSem'45''8866'_1552 = erased
-- Once.Adequacy.CoreMeaningBridge._.bindC
d_bindC_1586 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bindC_1586 = erased
-- Once.Adequacy.CoreMeaningBridge._.app-comb
d_app'45'comb_1612 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_app'45'comb_1612 = erased
-- Once.Adequacy.CoreMeaningBridge._.binK
d_binK_1644 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
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
d_binK_1644 = erased
-- Once.Adequacy.CoreMeaningBridge._.bridge-d
d_bridge'45'd_1678 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_278 ->
  T_Agree_140 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge'45'd_1678 = erased
-- Once.Adequacy.CoreMeaningBridge._.bridge-i
d_bridge'45'i_1698 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_278 ->
  T_Agree_140 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge'45'i_1698 = erased
-- Once.Adequacy.CoreMeaningBridge._.bridge-c
d_bridge'45'c_1718 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_278 ->
  T_Agree_140 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge'45'c_1718 = erased
-- Once.Adequacy.CoreMeaningBridge._._.Γc
d_Γc_2304 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_278 ->
  T_Agree_140 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Context.T_Ctx_6
d_Γc_2304 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
  = du_Γc_2304 v5
du_Γc_2304 ::
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6
du_Γc_2304 v0
  = coe MAlonzo.Code.Once.Spec.Typing.Scope.d_debruijn_122 (coe v0)
-- Once.Adequacy.CoreMeaningBridge._._.x
d_x_2306 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_278 ->
  T_Agree_140 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  AgdaAny -> AgdaAny
d_x_2306 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
         ~v14 ~v15 ~v16 ~v17 ~v18 v19 v20 v21 ~v22 ~v23 ~v24 v25
  = du_x_2306 v5 v19 v20 v21 v25
du_x_2306 ::
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 -> AgdaAny -> AgdaAny
du_x_2306 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.PhaseV.du_restrict'7515'_40
      (coe du_Γc_2304 (coe v0))
      (coe
         MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76 (coe v1)
         (coe
            MAlonzo.Code.Once.Spec.Context.du__'8852''7512'__100 (coe v2)
            (coe v3)))
      (coe
         MAlonzo.Code.Once.Spec.Context.du__'8852''7512'__100 (coe v2)
         (coe v3))
      (coe
         MAlonzo.Code.Once.Spec.Context.du_'8849''7512''45''43''691'_240
         (coe v1)
         (coe
            MAlonzo.Code.Once.Spec.Context.du__'8852''7512'__100 (coe v2)
            (coe v3)))
      (coe v4)
-- Once.Adequacy.CoreMeaningBridge._._..extendedlambda0
d_'46'extendedlambda0_2308 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Spec.Core.Meaning.T_DefSem_348 ->
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_278 ->
  T_Agree_140 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'46'extendedlambda0_2308 = erased
