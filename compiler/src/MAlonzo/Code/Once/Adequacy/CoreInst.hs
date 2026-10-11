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

module MAlonzo.Code.Once.Adequacy.CoreInst where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Core.AbsTy
import qualified MAlonzo.Code.Once.Spec.Core.Abstract
import qualified MAlonzo.Code.Once.Spec.Core.DerivedTyping
import qualified MAlonzo.Code.Once.Spec.Core.PolyTy
import qualified MAlonzo.Code.Once.Spec.Core.PolyTyping
import qualified MAlonzo.Code.Once.Spec.Core.Rename
import qualified MAlonzo.Code.Once.Spec.Core.Syntax
import qualified MAlonzo.Code.Once.Spec.Core.Typing
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Spec.Type.Grade
import qualified MAlonzo.Code.Once.Spec.Type.Sub
import qualified MAlonzo.Code.Once.Spec.Type.WellFormed
import qualified MAlonzo.Code.Once.Surface.Thinning
import qualified MAlonzo.Code.Once.TypeCheck.RigidSubst
import qualified MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core

-- Once.Adequacy.CoreInst.G.Ren
d_Ren_28 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  Integer -> Integer -> ()
d_Ren_28 = erased
-- Once.Adequacy.CoreInst.G.Tm
d_Tm_32 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.Adequacy.CoreInst.G.extR
d_extR_44 ::
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
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_extR_44 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_extR_44
du_extR_44 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_extR_44 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Spec.Core.Syntax.du_extR_120 v2 v3
-- Once.Adequacy.CoreInst.G.primCod
d_primCod_106 ::
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
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8
d_primCod_106 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_primCod_106
du_primCod_106 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8
du_primCod_106
  = coe MAlonzo.Code.Once.Spec.Core.Syntax.du_primCod_58
-- Once.Adequacy.CoreInst.G.primDom
d_primDom_108 ::
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
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8
d_primDom_108 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_primDom_108
du_primDom_108 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8
du_primDom_108
  = coe MAlonzo.Code.Once.Spec.Core.Syntax.du_primDom_56
-- Once.Adequacy.CoreInst.G.ren
d_ren_112 ::
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
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_ren_112 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_ren_112
du_ren_112 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_ren_112 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Spec.Core.Syntax.du_ren_132 v2 v3
-- Once.Adequacy.CoreInst.G.wk
d_wk_144 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_wk_144 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_wk_144
du_wk_144 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_wk_144 v0 = coe MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_242
-- Once.Adequacy.CoreInst.GT._⊢[_]_∷_!_
d__'8866''91'_'93'_'8759'_'33'__250 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
                                    a10 a11 a12
  = ()
-- Once.Adequacy.CoreInst.GT.⊢case⊔
d_'8866'case'8852'_260 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'case'8852'_260 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8866'case'8852'_260
du_'8866'case'8852'_260 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'case'8852'_260 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                        v13 v14 v15 v16
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.du_'8866'case'8852'_664 v2 v3 v4
      v5 v6 v8 v9 v14 v15 v16
-- Once.Adequacy.CoreInst.PT._⊩_⊢[_]_∷_!_
d__'8873'_'8866''91'_'93'_'8759'_'33'__362 a0 a1 a2 a3 a4 a5 a6 a7
                                           a8 a9 a10 a11 a12 a13 a14
  = ()
-- Once.Adequacy.CoreInst.PT._⟪_⟫ᶜ
d__'10218'_'10219''7580'_364 ::
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
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PCtx_350 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6
d__'10218'_'10219''7580'_364 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du__'10218'_'10219''7580'_364
du__'10218'_'10219''7580'_364 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PCtx_350 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6
du__'10218'_'10219''7580'_364 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Spec.Core.PolyTyping.du__'10218'_'10219''7580'_444
      v0 v2 v3
-- Once.Adequacy.CoreInst.PT._⟪_⟫ₜ
d__'10218'_'10219''8348'_366 ::
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
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PTm_390 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d__'10218'_'10219''8348'_366 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du__'10218'_'10219''8348'_366
du__'10218'_'10219''8348'_366 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PTm_390 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du__'10218'_'10219''8348'_366 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Spec.Core.PolyTyping.du__'10218'_'10219''8348'_490
      v0 v2 v3
-- Once.Adequacy.CoreInst.PT.PCtx
d_PCtx_370 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.Adequacy.CoreInst.PT.PTm
d_PTm_372 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.Adequacy.CoreInst.PT.instantiate
d_instantiate_390 ::
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
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PCtx_350 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PTm_390 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__730 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_instantiate_390 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_instantiate_390
du_instantiate_390 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PCtx_350 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PTm_390 ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__730 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_instantiate_390 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Spec.Core.PolyTyping.du_instantiate_1130 v0 v5 v6
      v7 v8 v9 v10
-- Once.Adequacy.CoreInst.RN.ren-⊢
d_ren'45''8866'_626 ::
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
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_ren'45''8866'_626 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_ren'45''8866'_626
du_ren'45''8866'_626 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_ren'45''8866'_626 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Spec.Core.Rename.du_ren'45''8866'_578 v2 v3 v4 v5
      v6 v7 v8 v9
-- Once.Adequacy.CoreInst.RN.∅⊆
d_'8709''8838'_632 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10
d_'8709''8838'_632 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8709''8838'_632
du_'8709''8838'_632 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10
du_'8709''8838'_632 v0 v1
  = coe MAlonzo.Code.Once.Spec.Core.Rename.du_'8709''8838'_912 v1
-- Once.Adequacy.CoreInst.RN.⊢close
d_'8866'close_634 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'close_634 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_'8866'close_634
du_'8866'close_634 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'close_634 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Spec.Core.Rename.du_'8866'close_930 v1 v2 v3 v4
      v5
-- Once.Adequacy.CoreInst.DT.wk-⊢′
d_wk'45''8866''8242'_640 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_wk'45''8866''8242'_640 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_wk'45''8866''8242'_640
du_wk'45''8866''8242'_640 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_wk'45''8866''8242'_640 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_wk'45''8866''8242'_548
      v1 v2 v3 v4 v5 v6 v7
-- Once.Adequacy.CoreInst.DT.⊢anaᶜ
d_'8866'ana'7580'_646 ::
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
d_'8866'ana'7580'_646 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8866'ana'7580'_646
du_'8866'ana'7580'_646 ::
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
du_'8866'ana'7580'_646
  = coe
      MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'ana'7580'_768
-- Once.Adequacy.CoreInst.DT.⊢applyEffᶜ
d_'8866'applyEff'7580'_648 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'applyEff'7580'_648 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8866'applyEff'7580'_648
du_'8866'applyEff'7580'_648 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'applyEff'7580'_648 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'applyEff'7580'_826
      v0 v2 v3
-- Once.Adequacy.CoreInst.DT.⊢applyᶜ
d_'8866'apply'7580'_650 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'apply'7580'_650 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8866'apply'7580'_650
du_'8866'apply'7580'_650 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'apply'7580'_650 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'apply'7580'_792
      v0 v2 v3
-- Once.Adequacy.CoreInst.DT.⊢caseᶜ
d_'8866'case'7580'_652 ::
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
d_'8866'case'7580'_652 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8866'case'7580'_652
du_'8866'case'7580'_652 ::
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
du_'8866'case'7580'_652 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'case'7580'_664
      v0 v1 v2 v3 v4 v5 v6 v7 v9 v10 v11
-- Once.Adequacy.CoreInst.DT.⊢cataᶜ
d_'8866'cata'7580'_654 ::
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
d_'8866'cata'7580'_654 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8866'cata'7580'_654
du_'8866'cata'7580'_654 ::
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
du_'8866'cata'7580'_654 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'cata'7580'_734
      v0 v2 v3 v4 v5 v7 v8
-- Once.Adequacy.CoreInst.DT.⊢composeᶜ
d_'8866'compose'7580'_656 ::
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
d_'8866'compose'7580'_656 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8866'compose'7580'_656
du_'8866'compose'7580'_656 ::
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
du_'8866'compose'7580'_656 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'compose'7580'_580
      v0 v1 v2 v3 v4 v5 v6 v7 v9 v10 v11
-- Once.Adequacy.CoreInst.DT.⊢curryᶜ
d_'8866'curry'7580'_658 ::
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
d_'8866'curry'7580'_658 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8866'curry'7580'_658
du_'8866'curry'7580'_658 ::
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
du_'8866'curry'7580'_658 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'curry'7580'_702
      v0 v2 v3 v4 v5 v6 v7 v9
-- Once.Adequacy.CoreInst.DT.⊢effAppᶜ
d_'8866'effApp'7580'_660 ::
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
d_'8866'effApp'7580'_660 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8866'effApp'7580'_660
du_'8866'effApp'7580'_660 ::
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
du_'8866'effApp'7580'_660 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'effApp'7580'_858
      v1 v2 v3 v4 v5 v6 v7 v8 v9
-- Once.Adequacy.CoreInst.DT.⊢inᶜ
d_'8866'in'7580'_672 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
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
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'in'7580'_672 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8866'in'7580'_672 v8
du_'8866'in'7580'_672 ::
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'in'7580'_672 v0
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
      (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'roll_462 v0
         (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))
-- Once.Adequacy.CoreInst.DT.⊢outEffᶜ
d_'8866'outEff'7580'_674 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
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
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'outEff'7580'_674 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8
  = du_'8866'outEff'7580'_674 v7 v8
du_'8866'outEff'7580'_674 ::
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'outEff'7580'_674 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
      (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
         (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'out_518 v0 v1
            (coe
               MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
               (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
               (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_eff_32))
               (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))))
-- Once.Adequacy.CoreInst.DT.⊢outᶜ
d_'8866'out'7580'_676 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
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
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'out'7580'_676 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8
  = du_'8866'out'7580'_676 v7 v8
du_'8866'out'7580'_676 ::
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'out'7580'_676 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
      (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'out_518 v0 v1
         (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))
-- Once.Adequacy.CoreInst.DT.⊢pairᶜ
d_'8866'pair'7580'_678 ::
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
d_'8866'pair'7580'_678 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8866'pair'7580'_678
du_'8866'pair'7580'_678 ::
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
du_'8866'pair'7580'_678 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Spec.Core.DerivedTyping.du_'8866'pair'7580'_626
      v0 v1 v2 v3 v4 v5 v6 v7 v9 v10 v11
-- Once.Adequacy.CoreInst.DT.⊢var′
d_'8866'var'8242'_684 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
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
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'var'8242'_684 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8866'var'8242'_684 v8
du_'8866'var'8242'_684 ::
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'var'8242'_684 v0
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
      (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
      (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18 (coe v0))
      (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)
-- Once.Adequacy.CoreInst._.SigGround
d_SigGround_688 ::
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
  ()
d_SigGround_688 = erased
-- Once.Adequacy.CoreInst._.absCtx
d_absCtx_692 ::
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
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PCtx_350
d_absCtx_692 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_absCtx_692
du_absCtx_692 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PCtx_350
du_absCtx_692 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Spec.Core.Abstract.du_absCtx_676 v0 v2 v3
-- Once.Adequacy.CoreInst.RS.ρ̂
d_ρ'770'_734 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8
d_ρ'770'_734 ~v0 v1 v2 v3 ~v4 = du_ρ'770'_734 v1 v2 v3
du_ρ'770'_734 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8
du_ρ'770'_734 v0 v1 v2
  = coe
      MAlonzo.Code.Once.TypeCheck.RigidSubst.du_ρ'770'_14 (coe v0)
      (coe v1) (coe v2)
-- Once.Adequacy.CoreInst.RS.ρ̂-wf
d_ρ'770''45'wf_744 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48
d_ρ'770''45'wf_744 ~v0 v1 v2 ~v3 v4 = du_ρ'770''45'wf_744 v1 v2 v4
du_ρ'770''45'wf_744 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48
du_ρ'770''45'wf_744 v0 v1 v2
  = coe
      MAlonzo.Code.Once.TypeCheck.RigidSubst.du_ρ'770''45'wf_42 (coe v0)
      (coe v1) (coe v2)
-- Once.Adequacy.CoreInst.RS.ρ̂-⟦⟧
d_ρ'770''45''10214''10215'_746 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ρ'770''45''10214''10215'_746 = erased
-- Once.Adequacy.CoreInst.RS.ρ̂S
d_ρ'770'S_754 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6
d_ρ'770'S_754 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 = du_ρ'770'S_754 v3 v4 v5
du_ρ'770'S_754 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6
du_ρ'770'S_754 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.TypeCheck.RigidSubst.du_ρ'770'S_194 (coe v0)
      (coe v1) (coe v2) v4
-- Once.Adequacy.CoreInst._.tr
d_tr_758 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_tr_758 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
         ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19
  = du_tr_758 v19
du_tr_758 ::
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_tr_758 v0 = coe v0
-- Once.Adequacy.CoreInst.ρ̂ₜ
d_ρ'770''8348'_810 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_ρ'770''8348'_810 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 ~v7 v8
  = du_ρ'770''8348'_810 v3 v4 v5 v8
du_ρ'770''8348'_810 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_ρ'770''8348'_810 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Spec.Core.PolyTyping.du__'10218'_'10219''8348'_490
      (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Core.Abstract.du_absTm_724 (coe v0) (coe v1)
         (coe v3))
      (coe v2)
-- Once.Adequacy.CoreInst.ρ̂-dom
d_ρ'770''45'dom_816 ::
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
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ρ'770''45'dom_816 = erased
-- Once.Adequacy.CoreInst.ρ̂-cod
d_ρ'770''45'cod_824 ::
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
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ρ'770''45'cod_824 = erased
-- Once.Adequacy.CoreInst.WithSG.ρ̂-ref
d_ρ'770''45'ref_840 ::
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
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ρ'770''45'ref_840 = erased
-- Once.Adequacy.CoreInst.WithSG.ρ̂ᶜ
d_ρ'770''7580'_862 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_ρ'770''7580'_862 ~v0 ~v1 ~v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 v11 v12
                   v13 v14
  = du_ρ'770''7580'_862 v3 v4 v5 v6 v11 v12 v13 v14
du_ρ'770''7580'_862 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_ρ'770''7580'_862 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252
        -> coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272 v12 v18
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68 v19
               -> case coe v5 of
                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 v20 v21 v22
                      -> case coe v21 of
                           MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48 v23 v24
                             -> coe
                                  MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272 v12
                                  (coe
                                     du_ρ'770''7580'_862 (coe v0) (coe v1) (coe v2) (coe v3)
                                     (coe v19) (coe v22) (coe v24) (coe v18))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'app_294 v10 v11 v12 v14 v18 v19
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_app_70 v20 v21
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'app_294 v10 v11 v12
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_344
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                          (coe v14))
                       (coe v2))
                    (coe
                       du_ρ'770''7580'_862 (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                       (coe
                          MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 (coe v14)
                          (coe
                             MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48 (coe v12)
                             (coe v6))
                          (coe v5))
                       (coe v6) (coe v18))
                    (coe
                       du_ρ'770''7580'_862 (coe v0) (coe v1) (coe v2) (coe v3) (coe v21)
                       (coe v14) (coe v6) (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'let_316 v10 v11 v12 v14 v18 v19
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_72 v20 v21
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'let_316 v10 v11 v12
                    (coe
                       MAlonzo.Code.Once.TypeCheck.RigidSubst.du_ρ'770'_14 (coe v0)
                       (coe v1) (coe v2) (coe v14))
                    (coe
                       du_ρ'770''7580'_862 (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                       (coe v14) (coe v6) (coe v18))
                    (coe
                       du_ρ'770''7580'_862 (coe v0) (coe v1) (coe v2) (coe v3) (coe v21)
                       (coe v5) (coe v6) (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'unit_322
        -> coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'unit_322
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'pair_342 v10 v11 v17 v18
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_pair_76 v19 v20
               -> case coe v5 of
                    MAlonzo.Code.Once.Spec.Type.C__'42'__24 v21 v22
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'pair_342 v10 v11
                           (coe
                              du_ρ'770''7580'_862 (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe v21) (coe v6) (coe v17))
                           (coe
                              du_ρ'770''7580'_862 (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe v22) (coe v6) (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'fst_358 v13 v15
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_fst_78 v16
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'fst_358
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_344
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                          (coe v13))
                       (coe v2))
                    (coe
                       du_ρ'770''7580'_862 (coe v0) (coe v1) (coe v2) (coe v3) (coe v16)
                       (coe MAlonzo.Code.Once.Spec.Type.C__'42'__24 (coe v5) (coe v13))
                       (coe v6) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'snd_374 v12 v15
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_snd_80 v16
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'snd_374
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_344
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                          (coe v12))
                       (coe v2))
                    (coe
                       du_ρ'770''7580'_862 (coe v0) (coe v1) (coe v2) (coe v3) (coe v16)
                       (coe MAlonzo.Code.Once.Spec.Type.C__'42'__24 (coe v12) (coe v5))
                       (coe v6) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'inl_390 v15
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_inl_82 v16
               -> case coe v5 of
                    MAlonzo.Code.Once.Spec.Type.C__'43'__26 v17 v18
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'inl_390
                           (coe
                              du_ρ'770''7580'_862 (coe v0) (coe v1) (coe v2) (coe v3) (coe v16)
                              (coe v17) (coe v6) (coe v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'inr_406 v15
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_inr_84 v16
               -> case coe v5 of
                    MAlonzo.Code.Once.Spec.Type.C__'43'__26 v17 v18
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'inr_406
                           (coe
                              du_ρ'770''7580'_862 (coe v0) (coe v1) (coe v2) (coe v3) (coe v16)
                              (coe v18) (coe v6) (coe v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'case_434 v10 v11 v12 v13 v15 v16 v21 v22 v23
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_case_86 v24 v25 v26
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'case_434 v10 v11 v12 v13
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_344
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                          (coe v15))
                       (coe v2))
                    (MAlonzo.Code.Once.Spec.Core.PolyTy.d__'10218'_'10219'_344
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                          (coe v16))
                       (coe v2))
                    (coe
                       du_ρ'770''7580'_862 (coe v0) (coe v1) (coe v2) (coe v3) (coe v24)
                       (coe MAlonzo.Code.Once.Spec.Type.C__'43'__26 (coe v15) (coe v16))
                       (coe v6) (coe v21))
                    (coe
                       du_ρ'770''7580'_862 (coe v0) (coe v1) (coe v2) (coe v3) (coe v25)
                       (coe v5) (coe v6) (coe v22))
                    (coe
                       du_ρ'770''7580'_862 (coe v0) (coe v1) (coe v2) (coe v3) (coe v26)
                       (coe v5) (coe v6) (coe v23))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'absurd_448 v14
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_absurd_88 v15
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'absurd_448
                    (coe
                       du_ρ'770''7580'_862 (coe v0) (coe v1) (coe v2) (coe v3) (coe v15)
                       (coe MAlonzo.Code.Once.Spec.Type.C_Void_22) (coe v6) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'roll_462 v14 v15
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_roll_90 v16
               -> case coe v5 of
                    MAlonzo.Code.Once.Spec.Type.C_μ'45'type_30 v17
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'roll_462
                           (coe
                              MAlonzo.Code.Once.TypeCheck.RigidSubst.du_ρ'770''45'wf_42 (coe v0)
                              (coe v1) (coe v3) (coe v17) (coe v14))
                           (coe
                              du_ρ'770''7580'_862 (coe v0) (coe v1) (coe v2) (coe v3) (coe v16)
                              (coe
                                 MAlonzo.Code.Once.Spec.Type.d_'10214'_'10215'T_62 (coe v17)
                                 (coe v5))
                              (coe v6) (coe v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'fold_482 v10 v11 v13 v17 v18 v19
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_fold_92 v20 v21
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'fold_482 v10 v11
                    (coe
                       MAlonzo.Code.Once.TypeCheck.RigidSubst.du_ρ'770'F_18 (coe v0)
                       (coe v1) (coe v2) (coe v13))
                    (coe
                       MAlonzo.Code.Once.TypeCheck.RigidSubst.du_ρ'770''45'wf_42 (coe v0)
                       (coe v1) (coe v3) (coe v13) (coe v17))
                    (coe
                       du_ρ'770''7580'_862 (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                       (coe
                          MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28
                          (coe
                             MAlonzo.Code.Once.Spec.Type.d_'10214'_'10215'T_62 (coe v13)
                             (coe v5))
                          (coe
                             MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48
                             (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) (coe v6))
                          (coe v5))
                       (coe v6) (coe v18))
                    (coe
                       du_ρ'770''7580'_862 (coe v0) (coe v1) (coe v2) (coe v3) (coe v21)
                       (coe MAlonzo.Code.Once.Spec.Type.C_μ'45'type_30 (coe v13)) (coe v6)
                       (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'unfold_504 v10 v11 v15 v18 v19 v20
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_unfold_94 v21 v22
               -> case coe v5 of
                    MAlonzo.Code.Once.Spec.Type.C_ν'45'type_32 v23 v24
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'unfold_504 v10 v11
                           (coe
                              MAlonzo.Code.Once.TypeCheck.RigidSubst.du_ρ'770'_14 (coe v0)
                              (coe v1) (coe v2) (coe v15))
                           (coe
                              MAlonzo.Code.Once.TypeCheck.RigidSubst.du_ρ'770''45'wf_42 (coe v0)
                              (coe v1) (coe v3) (coe v23) (coe v18))
                           (coe
                              du_ρ'770''7580'_862 (coe v0) (coe v1) (coe v2) (coe v3) (coe v21)
                              (coe
                                 MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 (coe v15)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48
                                    (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) (coe v24))
                                 (coe
                                    MAlonzo.Code.Once.Spec.Type.d_'10214'_'10215'T_62 (coe v23)
                                    (coe v15)))
                              (coe v6) (coe v19))
                           (coe
                              du_ρ'770''7580'_862 (coe v0) (coe v1) (coe v2) (coe v3) (coe v22)
                              (coe v15) (coe v6) (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'out_518 v12 v14 v15
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_out_96 v16
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'out_518
                    (coe
                       MAlonzo.Code.Once.TypeCheck.RigidSubst.du_ρ'770'F_18 (coe v0)
                       (coe v1) (coe v2) (coe v12))
                    (coe
                       MAlonzo.Code.Once.TypeCheck.RigidSubst.du_ρ'770''45'wf_42 (coe v0)
                       (coe v1) (coe v3) (coe v12) (coe v14))
                    (coe
                       du_ρ'770''7580'_862 (coe v0) (coe v1) (coe v2) (coe v3) (coe v16)
                       (coe MAlonzo.Code.Once.Spec.Type.C_ν'45'type_32 (coe v12) (coe v6))
                       (coe v6) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'coerce_534 v15 v16
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_coerce_98 v17 v18 v19
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'coerce_534
                    (coe
                       MAlonzo.Code.Once.TypeCheck.RigidSubst.du_ρ'770''45''60''58'_60
                       (coe v0) (coe v1) (coe v2) (coe v17) (coe v5) (coe v15))
                    (coe
                       du_ρ'770''7580'_862 (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                       (coe v17) (coe v6) (coe v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lit'45'int_542
        -> coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lit'45'int_542
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lit'45'float_550
        -> coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lit'45'float_550
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'prim_564 v14
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_prim_102 v15 v16
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'prim_564
                    (coe
                       du_ρ'770''7580'_862 (coe v0) (coe v1) (coe v2) (coe v3) (coe v16)
                       (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_primDom_56 (coe v15))
                       (coe v6) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sigop_576 v12 v13 v14 v15
        -> coe
             MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sigop_576 v12 v13 v14
             v15
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'ref_586 v12
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_ref_108 v13 v14
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'ref_586
                    (\ v15 v16 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.RigidSubst.du_ρ'770''45'base_36
                         (coe v0) (coe v1) (coe v3) (coe v14 v15) (coe v12 v15 v16))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'use_602 v10 v15 v16
        -> coe
             MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'use_602 v10 v15
             (coe
                du_ρ'770''7580'_862 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v6) (coe v16))
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618 v11 v15 v16
        -> coe
             MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618 v11 v15
             (coe
                du_ρ'770''7580'_862 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v11) (coe v16))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoreInst.WithSG.ρ̂S-abs
d_ρ'770'S'45'abs_1042 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ρ'770'S'45'abs_1042 = erased
-- Once.Adequacy.CoreInst.WithSG.IA
d_IA_1064 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_IA_1064 ~v0 ~v1 ~v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 v11 v12 v13 v14
  = du_IA_1064 v3 v4 v5 v6 v11 v12 v13 v14
du_IA_1064 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Spec.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_IA_1064 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Spec.Core.PolyTyping.du_instantiate_1130 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Core.Abstract.du_absTm_724 (coe v0) (coe v1)
         (coe v4))
      (coe
         MAlonzo.Code.Once.Spec.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
         (coe v5))
      (coe v6) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Once.Spec.Core.Abstract.du_abs'45''8866'_934 (coe v0)
         (coe v1) (coe v4) (coe v5) (coe v6) (coe v7))
-- Once.Adequacy.CoreInst.WithSG.tr-isubst′
d_tr'45'isubst'8242'_1106 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PCtx_350 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T_PTm_390 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Spec.Core.PolyTy.T_Ty_16) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__730 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tr'45'isubst'8242'_1106 = erased
-- Once.Adequacy.CoreInst.WithSG.close
d_close_1138 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_close_1138 = erased
-- Once.Adequacy.CoreInst.WithSG.closeF
d_closeF_1172 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_closeF_1172 = erased
-- Once.Adequacy.CoreInst.WithSG.tr-var-subst
d_tr'45'var'45'subst_1194 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tr'45'var'45'subst_1194 = erased
-- Once.Adequacy.CoreInst.WithSG.inst-abs
d_inst'45'abs_1212 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inst'45'abs_1212 = erased
-- Once.Adequacy.CoreInst.WithSG._.c3
d_c3_1264 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_c3_1264 = erased
-- Once.Adequacy.CoreInst.WithSG.ρ̂ₜ-ren
d_ρ'770''8348''45'ren_1368 ::
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
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ρ'770''8348''45'ren_1368 = erased
-- Once.Adequacy.CoreInst.WithSG.ρ̂θ
d_ρ'770'θ_1488 ::
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
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10
d_ρ'770'θ_1488 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11 v12
  = du_ρ'770'θ_1488 v10 v11 v12
du_ρ'770'θ_1488 ::
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10
du_ρ'770'θ_1488 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Surface.Thinning.C_done_12 -> coe v2
      MAlonzo.Code.Once.Surface.Thinning.C_skip_26 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Context.C__'44'_'94'__12 v11 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Thinning.C_skip_26
                    (coe du_ρ'770'θ_1488 (coe v0) (coe v11) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Thinning.C_keep_40 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Spec.Context.C__'44'_'94'__12 v11 v12 v13
               -> case coe v1 of
                    MAlonzo.Code.Once.Spec.Context.C__'44'_'94'__12 v15 v16 v17
                      -> coe
                           MAlonzo.Code.Once.Surface.Thinning.C_keep_40
                           (coe du_ρ'770'θ_1488 (coe v11) (coe v15) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoreInst.WithSG.thin-var-ρ̂
d_thin'45'var'45'ρ'770'_1506 ::
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
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thin'45'var'45'ρ'770'_1506 = erased
-- Once.Adequacy.CoreInst.WithSG.thin-usage-ρ̂
d_thin'45'usage'45'ρ'770'_1530 ::
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
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thin'45'usage'45'ρ'770'_1530 = erased
-- Once.Adequacy.CoreInst.WithSG.ρ̂θ-refl
d_ρ'770'θ'45'refl_1550 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ρ'770'θ'45'refl_1550 = erased
-- Once.Adequacy.CoreInst.WithSG._.ρ̂ᶜ-sU
d_ρ'770''7580''45'sU_1582 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_ρ'770''7580''45'sU_1582 = erased
-- Once.Adequacy.CoreInst.WithSG._.ρ̂ᶜ-st
d_ρ'770''7580''45'st_1598 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_ρ'770''7580''45'st_1598 = erased
-- Once.Adequacy.CoreInst.WithSG._.ρ̂ᶜ-sA
d_ρ'770''7580''45'sA_1618 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_ρ'770''7580''45'sA_1618 = erased
-- Once.Adequacy.CoreInst.WithSG._.ren-sA
d_ren'45'sA_1646 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_ren'45'sA_1646 = erased
-- Once.Adequacy.CoreInst.WithSG._.ρ̂ᶜ-sUf
d_ρ'770''7580''45'sUf_1670 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  Integer ->
  (MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Spec.Context.T_Usage_46) ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_ρ'770''7580''45'sUf_1670 = erased
-- Once.Adequacy.CoreInst.WithSG._.rmUf
d_rmUf_1692 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  Integer ->
  (MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Spec.Context.T_Usage_46) ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_rmUf_1692 = erased
-- Once.Adequacy.CoreInst.WithSG._.rmU
d_rmU_1710 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_rmU_1710 = erased
-- Once.Adequacy.CoreInst.WithSG._.rmt
d_rmt_1726 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_rmt_1726 = erased
-- Once.Adequacy.CoreInst.WithSG._.rmA
d_rmA_1746 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Spec.Type.T_Type_8) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_rmA_1746 = erased
-- Once.Adequacy.CoreInst.WithSG.rm
d_rm_1762 ::
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
  () ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_rm_1762 = erased
-- Once.Adequacy.CoreInst.WithSG.U≡
d_U'8801'_1782 ::
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
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_U'8801'_1782 = erased
-- Once.Adequacy.CoreInst.WithSG.T≡
d_T'8801'_1800 ::
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
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_T'8801'_1800 = erased
-- Once.Adequacy.CoreInst.WithSG.T≡e
d_T'8801'e_1820 ::
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
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_T'8801'e_1820 = erased
-- Once.Adequacy.CoreInst.WithSG._.ex
d_ex_1832 ::
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
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ex_1832 = erased
-- Once.Adequacy.CoreInst.WithSG._.≅var
d_'8773'var_1848 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_'8773'var_1848 = erased
-- Once.Adequacy.CoreInst.WithSG._.≅1
d_'8773'1_1884 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  (MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Spec.Context.T_Usage_46) ->
  (MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62) ->
  (MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
   MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244) ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_'8773'1_1884 = erased
-- Once.Adequacy.CoreInst.WithSG._.≅2
d_'8773'2_1950 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  (MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Spec.Context.T_Usage_46) ->
  (MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62) ->
  (MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
   MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
   MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244) ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_'8773'2_1950 = erased
-- Once.Adequacy.CoreInst.WithSG._.≅lam
d_'8773'lam_1982 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_'8773'lam_1982 = erased
-- Once.Adequacy.CoreInst.WithSG._.≅let
d_'8773'let_2016 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
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
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_'8773'let_2016 = erased
-- Once.Adequacy.CoreInst.WithSG._.≅case
d_'8773'case_2062 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_'8773'case_2062 = erased
-- Once.Adequacy.CoreInst.WithSG._.≅case⊔
d_'8773'case'8852'_2112 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_'8773'case'8852'_2112 = erased
-- Once.Adequacy.CoreInst.WithSG._.≅sub-use
d_'8773'sub'45'use_2138 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_'8773'sub'45'use_2138 = erased
-- Once.Adequacy.CoreInst.WithSG._._.irr
d_irr_2150 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Spec.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_irr_2150 = erased
-- Once.Adequacy.CoreInst.WithSG.ρ̂ᶜ-ren
d_ρ'770''7580''45'ren_2172 ::
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
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_ρ'770''7580''45'ren_2172 = erased
-- Once.Adequacy.CoreInst.WithSG.ren-θ≡
d_ren'45'θ'8801'_2512 ::
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
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_ren'45'θ'8801'_2512 = erased
-- Once.Adequacy.CoreInst.WithSG.wk≅
d_wk'8773'_2532 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_wk'8773'_2532 = erased
-- Once.Adequacy.CoreInst.WithSG.ρ̂θ-∅
d_ρ'770'θ'45''8709'_2556 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ρ'770'θ'45''8709'_2556 = erased
-- Once.Adequacy.CoreInst.WithSG.close≅
d_close'8773'_2576 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_close'8773'_2576 = erased
-- Once.Adequacy.CoreInst.WithSG._.c-compose
d_c'45'compose_2612 ::
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
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_c'45'compose_2612 = erased
-- Once.Adequacy.CoreInst.WithSG._.c-pair
d_c'45'pair_2660 ::
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
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_c'45'pair_2660 = erased
-- Once.Adequacy.CoreInst.WithSG._._.E
d_E_2682 ::
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
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_E_2682 = erased
-- Once.Adequacy.CoreInst.WithSG._.c-case
d_c'45'case_2708 ::
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
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_c'45'case_2708 = erased
-- Once.Adequacy.CoreInst.WithSG._._.E
d_E_2732 ::
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
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_E_2732 = erased
-- Once.Adequacy.CoreInst.WithSG._.c-curry
d_c'45'curry_2756 ::
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
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_c'45'curry_2756 = erased
-- Once.Adequacy.CoreInst.WithSG._._.E
d_E_2766 ::
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
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_E_2766 = erased
-- Once.Adequacy.CoreInst.WithSG._.c-apply
d_c'45'apply_2776 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_c'45'apply_2776 = erased
-- Once.Adequacy.CoreInst.WithSG._.c-applyEff
d_c'45'applyEff_2782 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_c'45'applyEff_2782 = erased
-- Once.Adequacy.CoreInst.WithSG._.c-effApp
d_c'45'effApp_2800 ::
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
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_c'45'effApp_2800 = erased
-- Once.Adequacy.CoreInst.WithSG._.in-gen
d_in'45'gen_2832 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_in'45'gen_2832 = erased
-- Once.Adequacy.CoreInst.WithSG._.out-gen
d_out'45'gen_2850 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_out'45'gen_2850 = erased
-- Once.Adequacy.CoreInst.WithSG._.outEff-gen
d_outEff'45'gen_2868 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_outEff'45'gen_2868 = erased
-- Once.Adequacy.CoreInst.WithSG._.c-in
d_c'45'in_2876 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_c'45'in_2876 = erased
-- Once.Adequacy.CoreInst.WithSG._.c-out
d_c'45'out_2886 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_c'45'out_2886 = erased
-- Once.Adequacy.CoreInst.WithSG._.c-outEff
d_c'45'outEff_2896 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_c'45'outEff_2896 = erased
-- Once.Adequacy.CoreInst.WithSG._.cata-gen
d_cata'45'gen_2928 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_cata'45'gen_2928 = erased
-- Once.Adequacy.CoreInst.WithSG._.ana-gen
d_ana'45'gen_2962 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_ana'45'gen_2962 = erased
-- Once.Adequacy.CoreInst.WithSG._.c-cata
d_c'45'cata_2984 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_c'45'cata_2984 = erased
-- Once.Adequacy.CoreInst.WithSG._._.E
d_E_3000 ::
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
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_E_3000 = erased
-- Once.Adequacy.CoreInst.WithSG._.c-ana
d_c'45'ana_3024 ::
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
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_c'45'ana_3024 = erased
