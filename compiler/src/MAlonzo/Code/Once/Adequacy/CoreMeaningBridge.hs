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
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Contract
import qualified MAlonzo.Code.Once.Lang.Core.DerivedTyping
import qualified MAlonzo.Code.Once.Lang.Core.Meaning
import qualified MAlonzo.Code.Once.Lang.Core.PolyTy
import qualified MAlonzo.Code.Once.Lang.Core.Syntax
import qualified MAlonzo.Code.Once.Lang.Core.Typing
import qualified MAlonzo.Code.Once.Lang.Elaboration
import qualified MAlonzo.Code.Once.Lang.Environment
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Poly
import qualified MAlonzo.Code.Once.Lang.Type.Sub
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Typing
import qualified MAlonzo.Code.Once.Lang.Typing.Scope
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Numerics

-- Once.Adequacy.CoreMeaningBridge.GM.DefSem
d_DefSem_16 a0 a1 a2 a3 = ()
-- Once.Adequacy.CoreMeaningBridge.GM.⟦_⟧
d_'10214'_'10215'_30 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  AgdaAny -> AgdaAny
d_'10214'_'10215'_30 ~v0 v1 ~v2 ~v3 = du_'10214'_'10215'_30 v1
du_'10214'_'10215'_30 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  AgdaAny -> AgdaAny
du_'10214'_'10215'_30 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Lang.Core.Meaning.du_'10214'_'10215'_498 (coe v0)
      v2 v3 v4 v5 v6 v7
-- Once.Adequacy.CoreMeaningBridge.GM.DefSem.defs
d_defs_34 ::
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8) ->
  AgdaAny
d_defs_34 v0
  = coe MAlonzo.Code.Once.Lang.Core.Meaning.d_defs_370 (coe v0)
-- Once.Adequacy.CoreMeaningBridge.GM.DefSem.impl
d_impl_36 ::
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  MAlonzo.Code.Once.Lang.Contract.T_Impl_242
d_impl_36 v0
  = coe MAlonzo.Code.Once.Lang.Core.Meaning.d_impl_372 (coe v0)
-- Once.Adequacy.CoreMeaningBridge._.Elab
d_Elab_44 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_Elab_44 = erased
-- Once.Adequacy.CoreMeaningBridge._.ImportAt
d_ImportAt_46 a0 a1 a2 a3 a4 a5 = ()
-- Once.Adequacy.CoreMeaningBridge._.InstanceOf
d_InstanceOf_50 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_InstanceOf_50 = erased
-- Once.Adequacy.CoreMeaningBridge._.View
d_View_52 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.Adequacy.CoreMeaningBridge._.Views
d_Views_56 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 -> ()
d_Views_56 = erased
-- Once.Adequacy.CoreMeaningBridge._.elabᵈ
d_elab'7496'_60 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_View_508 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elab'7496'_60 ~v0 v1 v2 v3 = du_elab'7496'_60 v1 v2 v3
du_elab'7496'_60 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_View_508 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_elab'7496'_60 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Elaboration.d_elab'7496'_808 (coe v0)
      (coe v1) (coe v2)
-- Once.Adequacy.CoreMeaningBridge._.elabᵢ
d_elab'7522'_62 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_View_508 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elab'7522'_62 ~v0 v1 v2 v3 = du_elab'7522'_62 v1 v2 v3
du_elab'7522'_62 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_View_508 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_elab'7522'_62 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Elaboration.d_elab'7522'_794 (coe v0)
      (coe v1) (coe v2)
-- Once.Adequacy.CoreMeaningBridge._.elabᶜ
d_elab'7580'_64 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_View_508 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elab'7580'_64 ~v0 v1 v2 v3 = du_elab'7580'_64 v1 v2 v3
du_elab'7580'_64 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_View_508 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_elab'7580'_64 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Elaboration.d_elab'7580'_784 (coe v0)
      (coe v1) (coe v2)
-- Once.Adequacy.CoreMeaningBridge._.subE
d_subE_66 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
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
  MAlonzo.Code.Once.Lang.Elaboration.T_ImportAt_486 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_entryOf_78 v0
  = coe MAlonzo.Code.Once.Lang.Elaboration.d_entryOf_496 (coe v0)
-- Once.Adequacy.CoreMeaningBridge._.ImportAt.instOf
d_instOf_80 ::
  MAlonzo.Code.Once.Lang.Elaboration.T_ImportAt_486 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_instOf_80 v0
  = coe MAlonzo.Code.Once.Lang.Elaboration.d_instOf_498 (coe v0)
-- Once.Adequacy.CoreMeaningBridge._.View.declares
d_declares_84 ::
  MAlonzo.Code.Once.Lang.Elaboration.T_View_508 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_Declared_462
d_declares_84 v0
  = coe MAlonzo.Code.Once.Lang.Elaboration.d_declares_576 (coe v0)
-- Once.Adequacy.CoreMeaningBridge._.View.entry
d_entry_86 ::
  MAlonzo.Code.Once.Lang.Elaboration.T_View_508 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_entry_86 v0
  = coe MAlonzo.Code.Once.Lang.Elaboration.d_entry_586 (coe v0)
-- Once.Adequacy.CoreMeaningBridge._.View.ground
d_ground_88 ::
  MAlonzo.Code.Once.Lang.Elaboration.T_View_508 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ground_88 v0
  = coe MAlonzo.Code.Once.Lang.Elaboration.d_ground_600 (coe v0)
-- Once.Adequacy.CoreMeaningBridge._.View.imported
d_imported_90 ::
  MAlonzo.Code.Once.Lang.Elaboration.T_View_508 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_ImportAt_486
d_imported_90 v0
  = coe MAlonzo.Code.Once.Lang.Elaboration.d_imported_570 (coe v0)
-- Once.Adequacy.CoreMeaningBridge._.View.inst
d_inst_92 ::
  MAlonzo.Code.Once.Lang.Elaboration.T_View_508 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inst_92 v0
  = coe MAlonzo.Code.Once.Lang.Elaboration.d_inst_614 (coe v0)
-- Once.Adequacy.CoreMeaningBridge.refSem
d_refSem_100 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_refSem_100 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7 = du_refSem_100 v4 v5 v7
du_refSem_100 ::
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_refSem_100 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe MAlonzo.Code.Once.Lang.Core.Meaning.d_defs_370 v0 v1 v3 v5
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoreMeaningBridge.impSem
d_impSem_120 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_ImportAt_486 -> AgdaAny
d_impSem_120 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 = du_impSem_120 v4 v7
du_impSem_120 ::
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_ImportAt_486 -> AgdaAny
du_impSem_120 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Elaboration.C_def_500 v2 v3
        -> coe du_refSem_100 (coe v0) (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoreMeaningBridge.Agree
d_Agree_140 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_Agree_140 = C_constructor_282
-- Once.Adequacy.CoreMeaningBridge.Agree.agree-inst
d_agree'45'inst_234 ::
  T_Agree_140 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'inst_234 = erased
-- Once.Adequacy.CoreMeaningBridge.Agree.agree-ground
d_agree'45'ground_248 ::
  T_Agree_140 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'ground_248 = erased
-- Once.Adequacy.CoreMeaningBridge.Agree.agree-import
d_agree'45'import_256 ::
  T_Agree_140 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'import_256 = erased
-- Once.Adequacy.CoreMeaningBridge.Agree.agree-qualified
d_agree'45'qualified_268 ::
  T_Agree_140 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'qualified_268 = erased
-- Once.Adequacy.CoreMeaningBridge.Agree.agree-resolved
d_agree'45'resolved_278 ::
  T_Agree_140 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'resolved_278 = erased
-- Once.Adequacy.CoreMeaningBridge.Agree.agree-world
d_agree'45'world_280 ::
  T_Agree_140 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'world_280 = erased
-- Once.Adequacy.CoreMeaningBridge._.Tm
d_Tm_296 a0 a1 a2 a3 a4 = ()
-- Once.Adequacy.CoreMeaningBridge._._⊢[_]_∷_!_
d__'8866''91'_'93'_'8759'_'33'__518 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
  = ()
-- Once.Adequacy.CoreMeaningBridge._.⊢anaᶜ
d_'8866'ana'7580'_636 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'ana'7580'_636 ~v0 ~v1 ~v2 ~v3 = du_'8866'ana'7580'_636
du_'8866'ana'7580'_636 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'ana'7580'_636 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Lang.Core.DerivedTyping.du_'8866'ana'7580'_788 v0
      v1 v2 v3 v4 v6 v7 v8 v9 v10
-- Once.Adequacy.CoreMeaningBridge._.⊢applyEffᶜ
d_'8866'applyEff'7580'_638 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'applyEff'7580'_638 ~v0 ~v1 ~v2 ~v3
  = du_'8866'applyEff'7580'_638
du_'8866'applyEff'7580'_638 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'applyEff'7580'_638 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Lang.Core.DerivedTyping.du_'8866'applyEff'7580'_850
      v0 v2 v3 v4
-- Once.Adequacy.CoreMeaningBridge._.⊢applyᶜ
d_'8866'apply'7580'_640 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'apply'7580'_640 ~v0 ~v1 ~v2 ~v3 = du_'8866'apply'7580'_640
du_'8866'apply'7580'_640 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'apply'7580'_640 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Core.DerivedTyping.du_'8866'apply'7580'_814
      v0 v2 v3
-- Once.Adequacy.CoreMeaningBridge._.⊢caseᶜ
d_'8866'case'7580'_642 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'case'7580'_642 ~v0 ~v1 ~v2 ~v3 = du_'8866'case'7580'_642
du_'8866'case'7580'_642 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'case'7580'_642 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Lang.Core.DerivedTyping.du_'8866'case'7580'_680
      v0 v1 v2 v3 v4 v5 v6 v7 v9 v10 v11
-- Once.Adequacy.CoreMeaningBridge._.⊢cataᶜ
d_'8866'cata'7580'_644 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'cata'7580'_644 ~v0 ~v1 ~v2 ~v3 = du_'8866'cata'7580'_644
du_'8866'cata'7580'_644 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'cata'7580'_644 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Lang.Core.DerivedTyping.du_'8866'cata'7580'_752
      v0 v2 v3 v4 v5 v7 v8 v9
-- Once.Adequacy.CoreMeaningBridge._.⊢composeᶜ
d_'8866'compose'7580'_646 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'compose'7580'_646 ~v0 ~v1 ~v2 ~v3
  = du_'8866'compose'7580'_646
du_'8866'compose'7580'_646 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'compose'7580'_646 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                           v12 v13 v14
  = coe
      MAlonzo.Code.Once.Lang.Core.DerivedTyping.du_'8866'compose'7580'_592
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v11 v12 v13 v14
-- Once.Adequacy.CoreMeaningBridge._.⊢curryᶜ
d_'8866'curry'7580'_648 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'curry'7580'_648 ~v0 ~v1 ~v2 ~v3 = du_'8866'curry'7580'_648
du_'8866'curry'7580'_648 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'curry'7580'_648 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Lang.Core.DerivedTyping.du_'8866'curry'7580'_718
      v0 v2 v3 v4 v5 v7 v9 v10
-- Once.Adequacy.CoreMeaningBridge._.⊢effAppᶜ
d_'8866'effApp'7580'_650 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'effApp'7580'_650 ~v0 ~v1 ~v2 ~v3
  = du_'8866'effApp'7580'_650
du_'8866'effApp'7580'_650 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'effApp'7580'_650 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Lang.Core.DerivedTyping.du_'8866'effApp'7580'_886
      v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
-- Once.Adequacy.CoreMeaningBridge._.⊢pairᶜ
d_'8866'pair'7580'_668 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'pair'7580'_668 ~v0 ~v1 ~v2 ~v3 = du_'8866'pair'7580'_668
du_'8866'pair'7580'_668 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'pair'7580'_668 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                        v13 v14
  = coe
      MAlonzo.Code.Once.Lang.Core.DerivedTyping.du_'8866'pair'7580'_642
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v11 v12 v13 v14
-- Once.Adequacy.CoreMeaningBridge.env-subst
d_env'45'subst_742 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'subst_742 = erased
-- Once.Adequacy.CoreMeaningBridge.drop-bind
d_drop'45'bind_780 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45'bind_780 = erased
-- Once.Adequacy.CoreMeaningBridge.env-subst₂
d_env'45'subst'8322'_820 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Context.T__'8849''7512'__178 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_env'45'subst'8322'_820 = erased
-- Once.Adequacy.CoreMeaningBridge.diag-bind
d_diag'45'bind_842 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_diag'45'bind_842 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.bindC
d_bindC_874 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bindC_874 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.fmapC
d_fmapC_892 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmapC_892 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.compose-sem
d_compose'45'sem_930 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_compose'45'sem_930 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb._.E
d_E_950 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_E_950 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.pair-sem
d_pair'45'sem_1006 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pair'45'sem_1006 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb._.E
d_E_1026 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_E_1026 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.case-arm
d_case'45'arm_1070 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_case'45'arm_1070 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.case-sem
d_case'45'sem_1116 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_case'45'sem_1116 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb._.E
d_E_1142 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_E_1142 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.curry-sem
d_curry'45'sem_1184 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_curry'45'sem_1184 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb._.E
d_E_1204 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_E_1204 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb._._∙_
d__'8729'__1210 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d__'8729'__1210 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.appC-sem
d_appC'45'sem_1248 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_appC'45'sem_1248 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.bind2β
d_bind2β_1290 ::
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
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
d_bind2β_1290 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.apply-sem
d_apply'45'sem_1324 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_apply'45'sem_1324 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.substΨ1
d_substΨ1_1358 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_substΨ1_1358 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.ana-sem″
d_ana'45'sem'8243'_1392 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ana'45'sem'8243'_1392 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.applyEff-sem
d_applyEff'45'sem_1432 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_applyEff'45'sem_1432 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.effApp-sem
d_effApp'45'sem_1472 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_effApp'45'sem_1472 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb.cata-sem′
d_cata'45'sem'8242'_1518 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cata'45'sem'8242'_1518 = erased
-- Once.Adequacy.CoreMeaningBridge.Comb._.E
d_E_1538 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_E_1538 = erased
-- Once.Adequacy.CoreMeaningBridge.assocT
d_assocT_1562 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assocT_1562 = erased
-- Once.Adequacy.CoreMeaningBridge.idʳT
d_id'691'T_1574 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_id'691'T_1574 = erased
-- Once.Adequacy.CoreMeaningBridge.subE-sem
d_subE'45'sem_1596 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subE'45'sem_1596 = erased
-- Once.Adequacy.CoreMeaningBridge.refSem-⊢
d_refSem'45''8866'_1618 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refSem'45''8866'_1618 = erased
-- Once.Adequacy.CoreMeaningBridge._.bindC
d_bindC_1652 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bindC_1652 = erased
-- Once.Adequacy.CoreMeaningBridge._.fmapC
d_fmapC_1670 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmapC_1670 = erased
-- Once.Adequacy.CoreMeaningBridge._.app-comb
d_app'45'comb_1694 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_app'45'comb_1694 = erased
-- Once.Adequacy.CoreMeaningBridge._.binK
d_binK_1724 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
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
d_binK_1724 = erased
-- Once.Adequacy.CoreMeaningBridge._.bridge-d
d_bridge'45'd_1754 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_View_508 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_294 ->
  T_Agree_140 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge'45'd_1754 = erased
-- Once.Adequacy.CoreMeaningBridge._.bridge-i
d_bridge'45'i_1774 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_View_508 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_294 ->
  T_Agree_140 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge'45'i_1774 = erased
-- Once.Adequacy.CoreMeaningBridge._.bridge-c
d_bridge'45'c_1794 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_View_508 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_294 ->
  T_Agree_140 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bridge'45'c_1794 = erased
-- Once.Adequacy.CoreMeaningBridge._._.Γc
d_Γc_2374 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_View_508 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_294 ->
  T_Agree_140 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Context.T_Ctx_6
d_Γc_2374 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23 ~v24 ~v25
  = du_Γc_2374 v5
du_Γc_2374 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6
du_Γc_2374 v0
  = coe MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122 (coe v0)
-- Once.Adequacy.CoreMeaningBridge._._.x
d_x_2376 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_View_508 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_294 ->
  T_Agree_140 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  AgdaAny -> AgdaAny
d_x_2376 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13
         ~v14 ~v15 ~v16 ~v17 ~v18 v19 v20 v21 ~v22 ~v23 ~v24 v25
  = du_x_2376 v5 v19 v20 v21 v25
du_x_2376 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 -> AgdaAny -> AgdaAny
du_x_2376 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Lang.Environment.du_restrict'7515'_40
      (coe du_Γc_2374 (coe v0))
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v1)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v2)
            (coe v3)))
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v2)
         (coe v3))
      (coe
         MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
         (coe v1)
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v2)
            (coe v3)))
      (coe v4)
-- Once.Adequacy.CoreMeaningBridge._._..extendedlambda0
d_'46'extendedlambda0_2378 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Lang.Core.Meaning.T_DefSem_356 ->
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Elaboration.T_View_508 ->
  MAlonzo.Code.Once.Denotation.Meaning.T_Meanings_294 ->
  T_Agree_140 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  AgdaAny ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'46'extendedlambda0_2378 = erased
