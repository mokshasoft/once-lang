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

module MAlonzo.Code.Once.Adequacy.ElabInst where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Once.Adequacy.ViewNatural
import qualified MAlonzo.Code.Once.Internal.Context
import qualified MAlonzo.Code.Once.Internal.Contract
import qualified MAlonzo.Code.Once.Internal.Core.AbsTy
import qualified MAlonzo.Code.Once.Internal.Core.Abstract
import qualified MAlonzo.Code.Once.Internal.Core.Meaning
import qualified MAlonzo.Code.Once.Internal.Core.PolyTy
import qualified MAlonzo.Code.Once.Internal.Core.PolyTyping
import qualified MAlonzo.Code.Once.Internal.Core.Schema
import qualified MAlonzo.Code.Once.Internal.Core.Syntax
import qualified MAlonzo.Code.Once.Internal.Core.Translate
import qualified MAlonzo.Code.Once.Internal.Core.Typing
import qualified MAlonzo.Code.Once.Internal.Elaboration
import qualified MAlonzo.Code.Once.Internal.Syntax
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Internal.Type.Poly
import qualified MAlonzo.Code.Once.Internal.Type.WellFormed
import qualified MAlonzo.Code.Once.Internal.Typing
import qualified MAlonzo.Code.Once.Internal.Typing.Scope
import qualified MAlonzo.Code.Once.Parser
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Instance

-- Once.Adequacy.ElabInst.PT.instantiate
d_instantiate_44 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTyping.T_PCtx_362 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.PolyTyping.T_PTm_402 ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Internal.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__650 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_instantiate_44 ~v0 ~v1 ~v2 = du_instantiate_44
du_instantiate_44 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTyping.T_PCtx_362 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.PolyTyping.T_PTm_402 ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Internal.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__650 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_instantiate_44 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Internal.Core.PolyTyping.du_instantiate_1090 v0
      v5 v6 v8 v9 v10
-- Once.Adequacy.ElabInst._.SigGround
d_SigGround_236 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer -> MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 -> ()
d_SigGround_236 = erased
-- Once.Adequacy.ElabInst._.abs-⊢
d_abs'45''8866'_238 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__650
d_abs'45''8866'_238 ~v0 ~v1 ~v2 = du_abs'45''8866'_238
du_abs'45''8866'_238 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__650
du_abs'45''8866'_238 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Internal.Core.Abstract.du_abs'45''8866'_934 v0 v1
      v6 v7 v9
-- Once.Adequacy.ElabInst.GM.DefSem
d_DefSem_242 a0 a1 a2 = ()
-- Once.Adequacy.ElabInst.GM.⟦_⟧
d_'10214'_'10215'_256 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Core.Meaning.T_DefSem_360 ->
  AgdaAny -> AgdaAny
d_'10214'_'10215'_256 v0 ~v1 ~v2 = du_'10214'_'10215'_256 v0
du_'10214'_'10215'_256 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Core.Meaning.T_DefSem_360 ->
  AgdaAny -> AgdaAny
du_'10214'_'10215'_256 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Internal.Core.Meaning.du_'10214'_'10215'_502
      (coe v0) v2 v3 v4 v5 v6 v7
-- Once.Adequacy.ElabInst.GM.DefSem.defs
d_defs_260 ::
  MAlonzo.Code.Once.Internal.Core.Meaning.T_DefSem_360 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8) ->
  AgdaAny
d_defs_260 v0
  = coe MAlonzo.Code.Once.Internal.Core.Meaning.d_defs_374 (coe v0)
-- Once.Adequacy.ElabInst.GM.DefSem.impl
d_impl_262 ::
  MAlonzo.Code.Once.Internal.Core.Meaning.T_DefSem_360 ->
  MAlonzo.Code.Once.Internal.Contract.T_Impl_242
d_impl_262 v0
  = coe MAlonzo.Code.Once.Internal.Core.Meaning.d_impl_376 (coe v0)
-- Once.Adequacy.ElabInst._.View
d_View_266 a0 a1 a2 a3 a4 a5 = ()
-- Once.Adequacy.ElabInst._.Views
d_Views_270 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 -> ()
d_Views_270 = erased
-- Once.Adequacy.ElabInst._.elabᶜ
d_elab'7580'_272 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Elaboration.T_View_516 ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elab'7580'_272 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Internal.Elaboration.d_elab'7580'_794 (coe v0)
      (coe v1) (coe v2)
-- Once.Adequacy.ElabInst._.View.declares
d_declares_276 ::
  MAlonzo.Code.Once.Internal.Elaboration.T_View_516 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Elaboration.T_Declared_470
d_declares_276 v0
  = coe
      MAlonzo.Code.Once.Internal.Elaboration.d_declares_584 (coe v0)
-- Once.Adequacy.ElabInst._.View.entry
d_entry_278 ::
  MAlonzo.Code.Once.Internal.Elaboration.T_View_516 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_entry_278 v0
  = coe MAlonzo.Code.Once.Internal.Elaboration.d_entry_594 (coe v0)
-- Once.Adequacy.ElabInst._.View.ground
d_ground_280 ::
  MAlonzo.Code.Once.Internal.Elaboration.T_View_516 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ground_280 v0
  = coe MAlonzo.Code.Once.Internal.Elaboration.d_ground_608 (coe v0)
-- Once.Adequacy.ElabInst._.View.imported
d_imported_282 ::
  MAlonzo.Code.Once.Internal.Elaboration.T_View_516 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Elaboration.T_ImportAt_494
d_imported_282 v0
  = coe
      MAlonzo.Code.Once.Internal.Elaboration.d_imported_578 (coe v0)
-- Once.Adequacy.ElabInst._.View.inst
d_inst_284 ::
  MAlonzo.Code.Once.Internal.Elaboration.T_View_516 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inst_284 v0
  = coe MAlonzo.Code.Once.Internal.Elaboration.d_inst_622 (coe v0)
-- Once.Adequacy.ElabInst._.NatImp
d_NatImp_288 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Elaboration.T_ImportAt_494 -> ()
d_NatImp_288 = erased
-- Once.Adequacy.ElabInst._.Natural
d_Natural_290 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
-- Once.Adequacy.ElabInst._.Natural.nat-ground
d_nat'45'ground_296 ::
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nat'45'ground_296 = erased
-- Once.Adequacy.ElabInst._.Natural.nat-imp
d_nat'45'imp_298 ::
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nat'45'imp_298 = erased
-- Once.Adequacy.ElabInst._.Natural.nat-inst
d_nat'45'inst_300 ::
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nat'45'inst_300 = erased
-- Once.Adequacy.ElabInst._.elab-ρ̂ᶜ
d_elab'45'ρ'770''7580'_342 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Internal.Elaboration.T_View_516 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  [MAlonzo.Code.Once.Internal.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_elab'45'ρ'770''7580'_342 = erased
-- Once.Adequacy.ElabInst.elab-inst-sem
d_elab'45'inst'45'sem_386 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Internal.Elaboration.T_View_516 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Core.Meaning.T_DefSem_360 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_elab'45'inst'45'sem_386 = erased
-- Once.Adequacy.ElabInst.elab-subst-sem
d_elab'45'subst'45'sem_438 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.Internal.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Elaboration.T_View_516 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Core.Meaning.T_DefSem_360 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_elab'45'subst'45'sem_438 = erased
-- Once.Adequacy.ElabInst.inst-at
d_inst'45'at_450 ::
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7580'_'8758'_'10814'__16
d_inst'45'at_450 ~v0 = du_inst'45'at_450
du_inst'45'at_450 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7580'_'8758'_'10814'__16
du_inst'45'at_450 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.TypeCheck.Instance.du_inst'45'at_24 v0 v1 v2 v3
      v4 v5 v7
-- Once.Adequacy.ElabInst.poly-instance-sem
d_poly'45'instance'45'sem_494 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Internal.Elaboration.T_View_516 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Core.Meaning.T_DefSem_360 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  (MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_poly'45'instance'45'sem_494 = erased
-- Once.Adequacy.ElabInst._.τ
d_τ_518 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Internal.Elaboration.T_View_516 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Core.Meaning.T_DefSem_360 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  (MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8
d_τ_518 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12 ~v13
        ~v14 ~v15 v16
  = du_τ_518 v11 v16
du_τ_518 ::
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8
du_τ_518 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Once.Internal.Core.Schema.du_kinded'45'instance_808
         (coe v0) (coe v1))
-- Once.Adequacy.ElabInst._.rk
d_rk_520 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Internal.Elaboration.T_View_516 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Core.Meaning.T_DefSem_360 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  (MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8
d_rk_520 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12 ~v13
         ~v14 ~v15 v16
  = du_rk_520 v11 v16
du_rk_520 ::
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8
du_rk_520 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Once.Internal.Core.Schema.du_kinded'45'instance_808
            (coe v0) (coe v1)))
-- Once.Adequacy.ElabInst._.e
d_e_522 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Internal.Elaboration.T_View_516 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Internal.Core.Meaning.T_DefSem_360 ->
  MAlonzo.Code.Once.Internal.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Internal.Type.Poly.T_PolyType_10 ->
  (MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Internal.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_e_522 = erased
-- Once.Adequacy.ElabInst._.Inst
d_Inst_538 ::
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Schema_808 -> ()
d_Inst_538 = erased
-- Once.Adequacy.ElabInst._.subst-pt
d_subst'45'pt_564 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Schema_808 ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Schema_808 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'pt_564 = erased
-- Once.Adequacy.ElabInst._.subst-fix
d_subst'45'fix_586 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Schema_808 ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Schema_808 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'fix_586 = erased
-- Once.Adequacy.ElabInst._.nat-imp′
d_nat'45'imp'8242'_602 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Internal.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nat'45'imp'8242'_602 = erased
-- Once.Adequacy.ElabInst._.viewOf-natural
d_viewOf'45'natural_688 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.T_PolyFunInfo_116] ->
  MAlonzo.Code.Once.Internal.Core.Translate.T_SigSig_64 ->
  MAlonzo.Code.Once.Internal.Core.Translate.T_ImpSig_84 ->
  MAlonzo.Code.Once.Internal.Core.Translate.T_TeleSig_110 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74
d_viewOf'45'natural_688 = erased
