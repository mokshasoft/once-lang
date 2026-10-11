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

module MAlonzo.Code.Once.Adequacy.ElabCommute where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Once.Adequacy.CoreInst
import qualified MAlonzo.Code.Once.Adequacy.ViewNatural
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Core.AbsTy
import qualified MAlonzo.Code.Once.Spec.Core.PolyTy
import qualified MAlonzo.Code.Once.Spec.Core.Syntax
import qualified MAlonzo.Code.Once.Spec.Core.Typing
import qualified MAlonzo.Code.Once.Spec.Elaboration
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Syntax
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Spec.Type.Grade
import qualified MAlonzo.Code.Once.Spec.Type.Sub
import qualified MAlonzo.Code.Once.Spec.Type.WellFormed
import qualified MAlonzo.Code.Once.Spec.Typing
import qualified MAlonzo.Code.Once.Spec.Typing.Scope
import qualified MAlonzo.Code.Once.TypeCheck.RigidSubst
import qualified MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core

-- Once.Adequacy.ElabCommute.G.Prim
d_Prim_40 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 = ()
-- Once.Adequacy.ElabCommute.G.Tm
d_Tm_46 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 = ()
-- Once.Adequacy.ElabCommute.G.wk
d_wk_158 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_wk_158 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
         ~v13
  = du_wk_158
du_wk_158 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_wk_158 v0 = coe MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_242
-- Once.Adequacy.ElabCommute.GT._⊢[_]_∷_!_
d__'8866''91'_'93'_'8759'_'33'__264 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
                                    a10 a11 a12 a13 a14 a15 a16 a17 a18 a19
  = ()
-- Once.Adequacy.ElabCommute._.Declared
d_Declared_438 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
               a15
  = ()
-- Once.Adequacy.ElabCommute._.ImportAt
d_ImportAt_442 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14
               a15
  = ()
-- Once.Adequacy.ElabCommute._.InstanceOf
d_InstanceOf_446 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 -> ()
d_InstanceOf_446 = erased
-- Once.Adequacy.ElabCommute._.elabᵈ
d_elab'7496'_454 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elab'7496'_454 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 ~v12 ~v13
  = du_elab'7496'_454 v0 v1 v2
du_elab'7496'_454 ::
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
du_elab'7496'_454 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Elaboration.d_elab'7496'_800 (coe v0)
      (coe v1) (coe v2)
-- Once.Adequacy.ElabCommute._.elabᵢ
d_elab'7522'_456 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elab'7522'_456 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 ~v12 ~v13
  = du_elab'7522'_456 v0 v1 v2
du_elab'7522'_456 ::
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
du_elab'7522'_456 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Elaboration.d_elab'7522'_786 (coe v0)
      (coe v1) (coe v2)
-- Once.Adequacy.ElabCommute._.elabᶜ
d_elab'7580'_458 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_elab'7580'_458 v0 v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 ~v12 ~v13
  = du_elab'7580'_458 v0 v1 v2
du_elab'7580'_458 ::
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
du_elab'7580'_458 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Elaboration.d_elab'7580'_776 (coe v0)
      (coe v1) (coe v2)
-- Once.Adequacy.ElabCommute._.importE
d_importE_460 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_ImportAt_478 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_importE_460 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
              ~v12 ~v13
  = du_importE_460
du_importE_460 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_ImportAt_478 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_importE_460 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Spec.Elaboration.du_importE_752 v4
-- Once.Adequacy.ElabCommute._.refE
d_refE_462 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_refE_462 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13
  = du_refE_462
du_refE_462 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_refE_462 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Spec.Elaboration.du_refE_720 v3 v4
-- Once.Adequacy.ElabCommute._.sigE
d_sigE_464 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_Declared_454 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sigE_464 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13
  = du_sigE_464
du_sigE_464 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_Declared_454 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sigE_464 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Spec.Elaboration.du_sigE_736 v0 v3 v4 v5
-- Once.Adequacy.ElabCommute._.Declared.honest
d_honest_468 ::
  MAlonzo.Code.Once.Spec.Elaboration.T_Declared_454 -> AgdaAny
d_honest_468 v0
  = coe MAlonzo.Code.Once.Spec.Elaboration.d_honest_466 (coe v0)
-- Once.Adequacy.ElabCommute._.Declared.member
d_member_470 ::
  MAlonzo.Code.Once.Spec.Elaboration.T_Declared_454 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_member_470 v0
  = coe MAlonzo.Code.Once.Spec.Elaboration.d_member_470 (coe v0)
-- Once.Adequacy.ElabCommute._.Declared.rigid
d_rigid_472 ::
  MAlonzo.Code.Once.Spec.Elaboration.T_Declared_454 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_RigidFree_68
d_rigid_472 v0
  = coe MAlonzo.Code.Once.Spec.Elaboration.d_rigid_468 (coe v0)
-- Once.Adequacy.ElabCommute._.ImportAt.entryOf
d_entryOf_476 ::
  MAlonzo.Code.Once.Spec.Elaboration.T_ImportAt_478 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_entryOf_476 v0
  = coe MAlonzo.Code.Once.Spec.Elaboration.d_entryOf_488 (coe v0)
-- Once.Adequacy.ElabCommute._.ImportAt.instOf
d_instOf_478 ::
  MAlonzo.Code.Once.Spec.Elaboration.T_ImportAt_478 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_instOf_478 v0
  = coe MAlonzo.Code.Once.Spec.Elaboration.d_instOf_490 (coe v0)
-- Once.Adequacy.ElabCommute._._⇝ᵢ_
d__'8669''7522'__494 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10
d__'8669''7522'__494 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18
  = du__'8669''7522'__494 v18
du__'8669''7522'__494 ::
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10
du__'8669''7522'__494 v0 = coe v0
-- Once.Adequacy.ElabCommute._._⇝ᶜ_
d__'8669''7580'__496 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16
d__'8669''7580'__496 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 v18
  = du__'8669''7580'__496 v18
du__'8669''7580'__496 ::
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16
du__'8669''7580'__496 v0 = coe v0
-- Once.Adequacy.ElabCommute._.subst-c′
d_subst'45'c'8242'_500 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16
d_subst'45'c'8242'_500 ~v0 ~v1 ~v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10
                       ~v11 ~v12 ~v13
  = du_subst'45'c'8242'_500 v3 v4 v5 v6
du_subst'45'c'8242'_500 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16
du_subst'45'c'8242'_500 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.TypeCheck.RigidSubst.d_subst'45'c'8242'_588
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.ElabCommute._.subst-d′
d_subst'45'd'8242'_502 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
d_subst'45'd'8242'_502 ~v0 ~v1 ~v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10
                       ~v11 ~v12 ~v13
  = du_subst'45'd'8242'_502 v3 v4 v5 v6
du_subst'45'd'8242'_502 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24
du_subst'45'd'8242'_502 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.TypeCheck.RigidSubst.d_subst'45'd'8242'_612
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.ElabCommute._.subst-i′
d_subst'45'i'8242'_504 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10
d_subst'45'i'8242'_504 ~v0 ~v1 ~v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10
                       ~v11 ~v12 ~v13
  = du_subst'45'i'8242'_504 v3 v4 v5 v6
du_subst'45'i'8242'_504 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10
du_subst'45'i'8242'_504 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.TypeCheck.RigidSubst.d_subst'45'i'8242'_568
      (coe v0) (coe v1) (coe v2) (coe v3)
-- Once.Adequacy.ElabCommute._.ρ̂
d_ρ'770'_506 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8
d_ρ'770'_506 ~v0 v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
  = du_ρ'770'_506 v1 v2 v3
du_ρ'770'_506 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8
du_ρ'770'_506 v0 v1 v2
  = coe
      MAlonzo.Code.Once.TypeCheck.RigidSubst.du_ρ'770'_14 (coe v0)
      (coe v1) (coe v2)
-- Once.Adequacy.ElabCommute._.ρ̂S
d_ρ'770'S_518 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6
d_ρ'770'S_518 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
              ~v13
  = du_ρ'770'S_518 v3 v4 v5
du_ρ'770'S_518 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6
du_ρ'770'S_518 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.TypeCheck.RigidSubst.du_ρ'770'S_194 (coe v0)
      (coe v1) (coe v2) v4
-- Once.Adequacy.ElabCommute.CI.ρ̂ₜ
d_ρ'770''8348'_526 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_ρ'770''8348'_526 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                   ~v12 ~v13
  = du_ρ'770''8348'_526 v3 v4 v5
du_ρ'770''8348'_526 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_ρ'770''8348'_526 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Adequacy.CoreInst.du_ρ'770''8348'_810 (coe v0)
      (coe v1) (coe v2) v4
-- Once.Adequacy.ElabCommute.CI.WithSG.ρ̂ᶜ
d_ρ'770''7580'_594 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_ρ'770''7580'_594 ~v0 ~v1 ~v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11
                   ~v12 ~v13
  = du_ρ'770''7580'_594 v3 v4 v5 v6
du_ρ'770''7580'_594 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_ρ'770''7580'_594 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Adequacy.CoreInst.du_ρ'770''7580'_862 (coe v0)
      (coe v1) (coe v2) (coe v3) v8 v9 v10 v11
-- Once.Adequacy.ElabCommute._.ρ̂ᶜ
d_ρ'770''7580'_690 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_ρ'770''7580'_690 ~v0 ~v1 ~v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 ~v11
                   ~v12 ~v13
  = du_ρ'770''7580'_690 v3 v4 v5 v6
du_ρ'770''7580'_690 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_ρ'770''7580'_690 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Adequacy.CoreInst.du_ρ'770''7580'_862 (coe v0)
      (coe v1) (coe v2) (coe v3) v7 v8 v9 v10
-- Once.Adequacy.ElabCommute.⇝ᵢ-tm
d_'8669''7522''45'tm_758 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8669''7522''45'tm_758 = erased
-- Once.Adequacy.ElabCommute.⇝ᵢ-dr
d_'8669''7522''45'dr_780 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_'8669''7522''45'dr_780 = erased
-- Once.Adequacy.ElabCommute.⇝ᶜ-tm
d_'8669''7580''45'tm_802 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8669''7580''45'tm_802 = erased
-- Once.Adequacy.ElabCommute.⇝ᶜ-dr
d_'8669''7580''45'dr_824 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_'8669''7580''45'dr_824 = erased
-- Once.Adequacy.ElabCommute.≅ref
d_'8773'ref_842 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_'8773'ref_842 = erased
-- Once.Adequacy.ElabCommute.refE-dr
d_refE'45'dr_898 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_refE'45'dr_898 = erased
-- Once.Adequacy.ElabCommute.sig-tm
d_sig'45'tm_934 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_Declared_454 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sig'45'tm_934 = erased
-- Once.Adequacy.ElabCommute.sig-dr
d_sig'45'dr_954 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsConcrete_34 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_Declared_454 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_sig'45'dr_954 = erased
-- Once.Adequacy.ElabCommute.imp-tm
d_imp'45'tm_974 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_ImportAt_478 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_imp'45'tm_974 = erased
-- Once.Adequacy.ElabCommute.imp-dr
d_imp'45'dr_992 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Elaboration.T_ImportAt_478 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_imp'45'dr_992 = erased
-- Once.Adequacy.ElabCommute.≅app
d_'8773'app_1068 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_'8773'app_1068 = erased
-- Once.Adequacy.ElabCommute.arms
d_arms_1082 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arms_1082 = erased
-- Once.Adequacy.ElabCommute.≅coerce
d_'8773'coerce_1126 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.Sub.T__'60''58'__20 ->
  MAlonzo.Code.Once.Spec.Type.Sub.T__'60''58'__20 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_'8773'coerce_1126 = erased
-- Once.Adequacy.ElabCommute.tm-i
d_tm'45'i_1150 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tm'45'i_1150 = erased
-- Once.Adequacy.ElabCommute.tm-c
d_tm'45'c_1166 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tm'45'c_1166 = erased
-- Once.Adequacy.ElabCommute.tm-d
d_tm'45'd_1186 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tm'45'd_1186 = erased
-- Once.Adequacy.ElabCommute.dr-i
d_dr'45'i_1202 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_dr'45'i_1202 = erased
-- Once.Adequacy.ElabCommute.dr-c
d_dr'45'c_1218 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_dr'45'c_1218 = erased
-- Once.Adequacy.ElabCommute.dr-d
d_dr'45'd_1238 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_dr'45'd_1238 = erased
-- Once.Adequacy.ElabCommute._.q
d_q_2010 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_q_2010 = erased
-- Once.Adequacy.ElabCommute._.TE
d_TE_2014 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_TE_2014 = erased
-- Once.Adequacy.ElabCommute._.q
d_q_2034 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_q_2034 = erased
-- Once.Adequacy.ElabCommute._.TE
d_TE_2038 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_TE_2038 = erased
-- Once.Adequacy.ElabCommute._.q
d_q_2138 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_q_2138 = erased
-- Once.Adequacy.ElabCommute._.TE
d_TE_2142 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_TE_2142 = erased
-- Once.Adequacy.ElabCommute.Σ≅
d_Σ'8773'_2158 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_Σ'8773'_2158 = erased
-- Once.Adequacy.ElabCommute.elab-ρ̂ᶜ
d_elab'45'ρ'770''7580'_2174 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Core.AbsTy.T_ConstFree_374) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Elaboration.T_View_500 ->
  MAlonzo.Code.Once.Adequacy.ViewNatural.T_Natural_74 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Integer ->
  [MAlonzo.Code.Once.Spec.Typing.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_elab'45'ρ'770''7580'_2174 = erased
