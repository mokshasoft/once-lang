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
import qualified MAlonzo.Code.Once.Internal.Context
import qualified MAlonzo.Code.Once.Internal.Core.AbsTy
import qualified MAlonzo.Code.Once.Internal.Core.Abstract
import qualified MAlonzo.Code.Once.Internal.Core.DerivedTyping
import qualified MAlonzo.Code.Once.Internal.Core.PolySub
import qualified MAlonzo.Code.Once.Internal.Core.PolyTy
import qualified MAlonzo.Code.Once.Internal.Core.PolyTyping
import qualified MAlonzo.Code.Once.Internal.Core.Rename
import qualified MAlonzo.Code.Once.Internal.Core.Syntax
import qualified MAlonzo.Code.Once.Internal.Core.Typing
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Internal.Type.Sub
import qualified MAlonzo.Code.Once.Internal.Type.WellFormed
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Surface.Thinning
import qualified MAlonzo.Code.Once.TypeCheck.RigidSubst
import qualified MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core

-- Once.Adequacy.CoreInst.G.Ren
d_Ren_28 ::
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8) ->
  Integer -> Integer -> ()
d_Ren_28 = erased
-- Once.Adequacy.CoreInst.G.Tm
d_Tm_32 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Once.Adequacy.CoreInst.G.extR
d_extR_44 ::
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
  = coe MAlonzo.Code.Once.Internal.Core.Syntax.du_extR_122 v2 v3
-- Once.Adequacy.CoreInst.G.primCod
d_primCod_108 ::
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
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8
d_primCod_108 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_primCod_108
du_primCod_108 ::
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8
du_primCod_108
  = coe MAlonzo.Code.Once.Internal.Core.Syntax.du_primCod_58
-- Once.Adequacy.CoreInst.G.primDom
d_primDom_110 ::
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
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8
d_primDom_110 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_primDom_110
du_primDom_110 ::
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8
du_primDom_110
  = coe MAlonzo.Code.Once.Internal.Core.Syntax.du_primDom_56
-- Once.Adequacy.CoreInst.G.ren
d_ren_114 ::
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
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62
d_ren_114 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_ren_114
du_ren_114 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62
du_ren_114 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Internal.Core.Syntax.du_ren_134 v2 v3
-- Once.Adequacy.CoreInst.G.wk
d_wk_146 ::
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
  Integer ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62
d_wk_146 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_wk_146
du_wk_146 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62
du_wk_146 v0 = coe MAlonzo.Code.Once.Internal.Core.Syntax.du_wk_274
-- Once.Adequacy.CoreInst.GT._⊢[_]_∷_!_
d__'8866''91'_'93'_'8759'_'33'__254 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9
                                    a10 a11 a12
  = ()
-- Once.Adequacy.CoreInst.GT.⊢app-pure
d_'8866'app'45'pure_262 ::
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
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'app'45'pure_262 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8866'app'45'pure_262
du_'8866'app'45'pure_262 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'app'45'pure_262 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Internal.Core.Typing.du_'8866'app'45'pure_780 v2
      v3 v4 v5 v9 v10 v11
-- Once.Adequacy.CoreInst.GT.⊢case⊔
d_'8866'case'8852'_266 ::
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
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'case'8852'_266 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8866'case'8852'_266
du_'8866'case'8852'_266 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'case'8852'_266 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                        v13 v14 v15 v16 v17
  = coe
      MAlonzo.Code.Once.Internal.Core.Typing.du_'8866'case'8852'_710 v2
      v3 v4 v5 v6 v7 v8 v9 v10 v15 v16 v17
-- Once.Adequacy.CoreInst.GT.⊢let-pure
d_'8866'let'45'pure_284 ::
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
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'let'45'pure_284 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8866'let'45'pure_284
du_'8866'let'45'pure_284 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'let'45'pure_284 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Internal.Core.Typing.du_'8866'let'45'pure_746 v2
      v3 v4 v5 v9 v10 v11
-- Once.Adequacy.CoreInst.PT._⊩_⊢[_]_∷_!_
d__'8873'_'8866''91'_'93'_'8759'_'33'__372 a0 a1 a2 a3 a4 a5 a6 a7
                                           a8 a9 a10 a11 a12 a13 a14
  = ()
-- Once.Adequacy.CoreInst.PT._⟪_⟫ᶜ
d__'10218'_'10219''7580'_374 ::
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
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTyping.T_PCtx_362 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6
d__'10218'_'10219''7580'_374 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du__'10218'_'10219''7580'_374
du__'10218'_'10219''7580'_374 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTyping.T_PCtx_362 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6
du__'10218'_'10219''7580'_374 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Internal.Core.PolyTyping.du__'10218'_'10219''7580'_458
      v0 v2 v3
-- Once.Adequacy.CoreInst.PT._⟪_⟫ₜ
d__'10218'_'10219''8348'_376 ::
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
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTyping.T_PTm_402 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62
d__'10218'_'10219''8348'_376 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du__'10218'_'10219''8348'_376
du__'10218'_'10219''8348'_376 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTyping.T_PTm_402 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62
du__'10218'_'10219''8348'_376 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Internal.Core.PolyTyping.du__'10218'_'10219''8348'_504
      v0 v2 v3
-- Once.Adequacy.CoreInst.PT.PCtx
d_PCtx_378 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.Adequacy.CoreInst.PT.PTm
d_PTm_380 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.Adequacy.CoreInst.PT.instantiate
d_instantiate_398 ::
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
d_instantiate_398 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_instantiate_398
du_instantiate_398 ::
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
du_instantiate_398 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Internal.Core.PolyTyping.du_instantiate_1090 v0
      v5 v6 v8 v9 v10
-- Once.Adequacy.CoreInst.RN.ren-⊢
d_ren'45''8866'_596 ::
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
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_ren'45''8866'_596 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_ren'45''8866'_596
du_ren'45''8866'_596 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_ren'45''8866'_596 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Internal.Core.Rename.du_ren'45''8866'_620 v2 v3
      v4 v5 v6 v8 v9
-- Once.Adequacy.CoreInst.RN.∅⊆
d_'8709''8838'_602 ::
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
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10
d_'8709''8838'_602 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8709''8838'_602
du_'8709''8838'_602 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10
du_'8709''8838'_602 v0 v1
  = coe MAlonzo.Code.Once.Internal.Core.Rename.du_'8709''8838'_982 v1
-- Once.Adequacy.CoreInst.RN.⊢close
d_'8866'close_604 ::
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
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'close_604 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_'8866'close_604
du_'8866'close_604 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'close_604 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Internal.Core.Rename.du_'8866'close_1000 v1 v2 v3
      v5
-- Once.Adequacy.CoreInst.DT.wk-⊢′
d_wk'45''8866''8242'_610 ::
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
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_wk'45''8866''8242'_610 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_wk'45''8866''8242'_610
du_wk'45''8866''8242'_610 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_wk'45''8866''8242'_610 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Internal.Core.DerivedTyping.du_wk'45''8866''8242'_562
      v1 v2 v3 v4 v6 v7
-- Once.Adequacy.CoreInst.DT.⊢anaᶜ
d_'8866'ana'7580'_616 ::
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
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'ana'7580'_616 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8866'ana'7580'_616
du_'8866'ana'7580'_616 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'ana'7580'_616 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Internal.Core.DerivedTyping.du_'8866'ana'7580'_794
      v0 v1 v2 v3 v4 v6 v7 v8 v9 v10
-- Once.Adequacy.CoreInst.DT.⊢applyEffᶜ
d_'8866'applyEff'7580'_618 ::
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
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'applyEff'7580'_618 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8866'applyEff'7580'_618
du_'8866'applyEff'7580'_618 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'applyEff'7580'_618 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Internal.Core.DerivedTyping.du_'8866'applyEff'7580'_882
      v0 v2 v3 v4
-- Once.Adequacy.CoreInst.DT.⊢applyᶜ
d_'8866'apply'7580'_620 ::
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
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'apply'7580'_620 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8866'apply'7580'_620
du_'8866'apply'7580'_620 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'apply'7580'_620 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Internal.Core.DerivedTyping.du_'8866'apply'7580'_846
      v0 v2 v3
-- Once.Adequacy.CoreInst.DT.⊢caseᶜ
d_'8866'case'7580'_622 ::
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
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'case'7580'_622 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8866'case'7580'_622
du_'8866'case'7580'_622 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'case'7580'_622 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = coe
      MAlonzo.Code.Once.Internal.Core.DerivedTyping.du_'8866'case'7580'_686
      v0 v1 v2 v3 v4 v5 v6 v7 v9 v10 v11
-- Once.Adequacy.CoreInst.DT.⊢cataᶜ
d_'8866'cata'7580'_624 ::
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
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'cata'7580'_624 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8866'cata'7580'_624
du_'8866'cata'7580'_624 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'cata'7580'_624 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Internal.Core.DerivedTyping.du_'8866'cata'7580'_758
      v0 v2 v3 v4 v5 v7 v8 v9
-- Once.Adequacy.CoreInst.DT.⊢composeᶜ
d_'8866'compose'7580'_626 ::
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
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'compose'7580'_626 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8866'compose'7580'_626
du_'8866'compose'7580'_626 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'compose'7580'_626 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                           v12 v13 v14
  = coe
      MAlonzo.Code.Once.Internal.Core.DerivedTyping.du_'8866'compose'7580'_598
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v11 v12 v13 v14
-- Once.Adequacy.CoreInst.DT.⊢curryᶜ
d_'8866'curry'7580'_628 ::
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
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'curry'7580'_628 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8866'curry'7580'_628
du_'8866'curry'7580'_628 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'curry'7580'_628 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Internal.Core.DerivedTyping.du_'8866'curry'7580'_724
      v0 v2 v3 v4 v5 v7 v9 v10
-- Once.Adequacy.CoreInst.DT.⊢effAppᶜ
d_'8866'effApp'7580'_630 ::
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
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'effApp'7580'_630 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8866'effApp'7580'_630
du_'8866'effApp'7580'_630 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'effApp'7580'_630 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Internal.Core.DerivedTyping.du_'8866'effApp'7580'_918
      v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
-- Once.Adequacy.CoreInst.DT.⊢inᶜ
d_'8866'in'7580'_642 ::
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'in'7580'_642 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8866'in'7580'_642 v8
du_'8866'in'7580'_642 ::
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'in'7580'_642 v0
  = coe
      MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'lam_276
      (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
      (coe
         MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'roll_476 v0
         (coe MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'var_256))
-- Once.Adequacy.CoreInst.DT.⊢loopᶜ
d_'8866'loop'7580'_644 ::
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
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'loop'7580'_644 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8866'loop'7580'_644
du_'8866'loop'7580'_644 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'loop'7580'_644 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Internal.Core.DerivedTyping.du_'8866'loop'7580'_824
      v0 v2 v3 v4 v6
-- Once.Adequacy.CoreInst.DT.⊢outEffᶜ
d_'8866'outEff'7580'_646 ::
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'outEff'7580'_646 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9
  = du_'8866'outEff'7580'_646 v7 v8 v9
du_'8866'outEff'7580'_646 ::
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'outEff'7580'_646 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'lam_276
      (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
      (coe
         MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'lam_276
         (coe MAlonzo.Code.Once.Spec.Grade.C_Zero_8)
         (coe
            MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'out_540 v0
            (coe
               MAlonzo.Code.Once.Spec.Grade.C_fin_42
               (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36))
            v1 v2
            (coe MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'var_256)))
-- Once.Adequacy.CoreInst.DT.⊢outᶜ
d_'8866'out'7580'_648 ::
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'out'7580'_648 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8
  = du_'8866'out'7580'_648 v7 v8
du_'8866'out'7580'_648 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'out'7580'_648 v0 v1
  = coe
      MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'lam_276
      (coe MAlonzo.Code.Once.Spec.Grade.C_One_10)
      (coe
         MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'out_540
         (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)
         (coe
            MAlonzo.Code.Once.Spec.Grade.C_fin_42
            (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36))
         v0 v1 (coe MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'var_256))
-- Once.Adequacy.CoreInst.DT.⊢pairᶜ
d_'8866'pair'7580'_650 ::
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
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'pair'7580'_650 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8866'pair'7580'_650
du_'8866'pair'7580'_650 ::
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'pair'7580'_650 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                        v13 v14
  = coe
      MAlonzo.Code.Once.Internal.Core.DerivedTyping.du_'8866'pair'7580'_648
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v11 v12 v13 v14
-- Once.Adequacy.CoreInst._.SigGround
d_SigGround_660 ::
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
  ()
d_SigGround_660 = erased
-- Once.Adequacy.CoreInst._.absCtx
d_absCtx_664 ::
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
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Core.PolyTyping.T_PCtx_362
d_absCtx_664 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_absCtx_664
du_absCtx_664 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Core.PolyTyping.T_PCtx_362
du_absCtx_664 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Internal.Core.Abstract.du_absCtx_646 v0 v2 v3
-- Once.Adequacy.CoreInst.RS.ρ̂
d_ρ'770'_706 ::
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
  MAlonzo.Code.Once.Internal.Type.T_Type_8
d_ρ'770'_706 ~v0 v1 v2 v3 ~v4 = du_ρ'770'_706 v1 v2 v3
du_ρ'770'_706 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8
du_ρ'770'_706 v0 v1 v2
  = coe
      MAlonzo.Code.Once.TypeCheck.RigidSubst.du_ρ'770'_14 (coe v0)
      (coe v1) (coe v2)
-- Once.Adequacy.CoreInst.RS.ρ̂-wf
d_ρ'770''45'wf_718 ::
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48
d_ρ'770''45'wf_718 ~v0 v1 v2 ~v3 v4 = du_ρ'770''45'wf_718 v1 v2 v4
du_ρ'770''45'wf_718 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48
du_ρ'770''45'wf_718 v0 v1 v2
  = coe
      MAlonzo.Code.Once.TypeCheck.RigidSubst.du_ρ'770''45'wf_42 (coe v0)
      (coe v1) (coe v2)
-- Once.Adequacy.CoreInst.RS.ρ̂-⟦⟧
d_ρ'770''45''10214''10215'_722 ::
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ρ'770''45''10214''10215'_722 = erased
-- Once.Adequacy.CoreInst.RS.ρ̂S
d_ρ'770'S_730 ::
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
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6
d_ρ'770'S_730 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 = du_ρ'770'S_730 v3 v4 v5
du_ρ'770'S_730 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6
du_ρ'770'S_730 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.TypeCheck.RigidSubst.du_ρ'770'S_232 (coe v0)
      (coe v1) (coe v2) v4
-- Once.Adequacy.CoreInst._.tr
d_tr_734 ::
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
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_tr_734 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
         ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 v19
  = du_tr_734 v19
du_tr_734 ::
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_tr_734 v0 = coe v0
-- Once.Adequacy.CoreInst.ρ̂ₜ
d_ρ'770''8348'_788 ::
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
  Integer ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62
d_ρ'770''8348'_788 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 ~v7 v8
  = du_ρ'770''8348'_788 v3 v4 v5 v8
du_ρ'770''8348'_788 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62
du_ρ'770''8348'_788 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Internal.Core.PolyTyping.du__'10218'_'10219''8348'_504
      (coe v0)
      (coe
         MAlonzo.Code.Once.Internal.Core.Abstract.du_absTm_694 (coe v0)
         (coe v1) (coe v3))
      (coe v2)
-- Once.Adequacy.CoreInst.ρ̂-dom
d_ρ'770''45'dom_794 ::
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
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ρ'770''45'dom_794 = erased
-- Once.Adequacy.CoreInst.ρ̂-cod
d_ρ'770''45'cod_802 ::
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
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Prim_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ρ'770''45'cod_802 = erased
-- Once.Adequacy.CoreInst.WithSG.ρ̂-ref
d_ρ'770''45'ref_818 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ρ'770''45'ref_818 = erased
-- Once.Adequacy.CoreInst.WithSG.ρ̂ᶜ
d_ρ'770''7580'_840 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_ρ'770''7580'_840 ~v0 ~v1 ~v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 v11 v12
                   ~v13 v14
  = du_ρ'770''7580'_840 v3 v4 v5 v6 v11 v12 v14
du_ρ'770''7580'_840 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_ρ'770''7580'_840 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'var_256
        -> coe MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'var_256
      MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'lam_276 v11 v17
        -> case coe v4 of
             MAlonzo.Code.Once.Internal.Core.Syntax.C_lam_68 v18 v19 v20 v21
               -> case coe v5 of
                    MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v22 v23 v24
                      -> coe
                           MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'lam_276 v11
                           (coe
                              du_ρ'770''7580'_840 (coe v0) (coe v1) (coe v2) (coe v3) (coe v21)
                              (coe v24) (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'app_302 v9 v10 v11 v12 v13 v14 v15 v19 v20
        -> case coe v4 of
             MAlonzo.Code.Once.Internal.Core.Syntax.C_app_70 v21 v22
               -> coe
                    MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'app_302 v9 v10 v11
                    v12 v13 v14
                    (MAlonzo.Code.Once.Internal.Core.PolyTy.d__'10218'_'10219'_344
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Internal.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                          (coe v15))
                       (coe v2))
                    (coe
                       du_ρ'770''7580'_840 (coe v0) (coe v1) (coe v2) (coe v3) (coe v21)
                       (coe
                          MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v15)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v11) (coe v12))
                          (coe v5))
                       (coe v19))
                    (coe
                       du_ρ'770''7580'_840 (coe v0) (coe v1) (coe v2) (coe v3) (coe v22)
                       (coe v15) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'let_326 v9 v10 v12 v13 v14 v18 v19
        -> case coe v4 of
             MAlonzo.Code.Once.Internal.Core.Syntax.C_let'8242'_72 v20 v21 v22
               -> coe
                    MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'let_326 v9 v10 v12
                    v13
                    (coe
                       MAlonzo.Code.Once.TypeCheck.RigidSubst.du_ρ'770'_14 (coe v0)
                       (coe v1) (coe v2) (coe v14))
                    (coe
                       du_ρ'770''7580'_840 (coe v0) (coe v1) (coe v2) (coe v3) (coe v21)
                       (coe v14) (coe v18))
                    (coe
                       du_ρ'770''7580'_840 (coe v0) (coe v1) (coe v2) (coe v3) (coe v22)
                       (coe v5) (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'unit_332
        -> coe MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'unit_332
      MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'pair_354 v9 v10 v11 v12 v17 v18
        -> case coe v4 of
             MAlonzo.Code.Once.Internal.Core.Syntax.C_pair_76 v19 v20
               -> case coe v5 of
                    MAlonzo.Code.Once.Internal.Type.C__'42'__24 v21 v22
                      -> coe
                           MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'pair_354 v9 v10 v11
                           v12
                           (coe
                              du_ρ'770''7580'_840 (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                              (coe v21) (coe v17))
                           (coe
                              du_ρ'770''7580'_840 (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                              (coe v22) (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'fst_370 v12 v14
        -> case coe v4 of
             MAlonzo.Code.Once.Internal.Core.Syntax.C_fst_78 v15
               -> coe
                    MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'fst_370
                    (MAlonzo.Code.Once.Internal.Core.PolyTy.d__'10218'_'10219'_344
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Internal.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                          (coe v12))
                       (coe v2))
                    (coe
                       du_ρ'770''7580'_840 (coe v0) (coe v1) (coe v2) (coe v3) (coe v15)
                       (coe
                          MAlonzo.Code.Once.Internal.Type.C__'42'__24 (coe v5) (coe v12))
                       (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'snd_386 v11 v14
        -> case coe v4 of
             MAlonzo.Code.Once.Internal.Core.Syntax.C_snd_80 v15
               -> coe
                    MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'snd_386
                    (MAlonzo.Code.Once.Internal.Core.PolyTy.d__'10218'_'10219'_344
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Internal.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                          (coe v11))
                       (coe v2))
                    (coe
                       du_ρ'770''7580'_840 (coe v0) (coe v1) (coe v2) (coe v3) (coe v15)
                       (coe
                          MAlonzo.Code.Once.Internal.Type.C__'42'__24 (coe v11) (coe v5))
                       (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'inl_402 v14
        -> case coe v4 of
             MAlonzo.Code.Once.Internal.Core.Syntax.C_inl_82 v15 v16
               -> case coe v5 of
                    MAlonzo.Code.Once.Internal.Type.C__'43'__26 v17 v18
                      -> coe
                           MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'inl_402
                           (coe
                              du_ρ'770''7580'_840 (coe v0) (coe v1) (coe v2) (coe v3) (coe v16)
                              (coe v17) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'inr_418 v14
        -> case coe v4 of
             MAlonzo.Code.Once.Internal.Core.Syntax.C_inr_84 v15 v16
               -> case coe v5 of
                    MAlonzo.Code.Once.Internal.Type.C__'43'__26 v17 v18
                      -> coe
                           MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'inr_418
                           (coe
                              du_ρ'770''7580'_840 (coe v0) (coe v1) (coe v2) (coe v3) (coe v16)
                              (coe v18) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'case_448 v9 v10 v13 v14 v15 v16 v21 v22 v23
        -> case coe v4 of
             MAlonzo.Code.Once.Internal.Core.Syntax.C_case_86 v24 v25 v26 v27 v28
               -> coe
                    MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'case_448 v9 v10 v13
                    v14
                    (MAlonzo.Code.Once.Internal.Core.PolyTy.d__'10218'_'10219'_344
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Internal.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                          (coe v15))
                       (coe v2))
                    (MAlonzo.Code.Once.Internal.Core.PolyTy.d__'10218'_'10219'_344
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Internal.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                          (coe v16))
                       (coe v2))
                    (coe
                       du_ρ'770''7580'_840 (coe v0) (coe v1) (coe v2) (coe v3) (coe v26)
                       (coe
                          MAlonzo.Code.Once.Internal.Type.C__'43'__26 (coe v15) (coe v16))
                       (coe v21))
                    (coe
                       du_ρ'770''7580'_840 (coe v0) (coe v1) (coe v2) (coe v3) (coe v27)
                       (coe v5) (coe v22))
                    (coe
                       du_ρ'770''7580'_840 (coe v0) (coe v1) (coe v2) (coe v3) (coe v28)
                       (coe v5) (coe v23))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'absurd_462 v13
        -> case coe v4 of
             MAlonzo.Code.Once.Internal.Core.Syntax.C_absurd_88 v14 v15
               -> coe
                    MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'absurd_462
                    (coe
                       du_ρ'770''7580'_840 (coe v0) (coe v1) (coe v2) (coe v3) (coe v15)
                       (coe MAlonzo.Code.Once.Internal.Type.C_Void_22) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'roll_476 v13 v14
        -> case coe v4 of
             MAlonzo.Code.Once.Internal.Core.Syntax.C_roll_90 v15 v16
               -> coe
                    MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'roll_476
                    (coe
                       MAlonzo.Code.Once.TypeCheck.RigidSubst.du_ρ'770''45'wf_42 (coe v0)
                       (coe v1) (coe v3) (coe v15) (coe v13))
                    (coe
                       du_ρ'770''7580'_840 (coe v0) (coe v1) (coe v2) (coe v3) (coe v16)
                       (coe
                          MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62 (coe v15)
                          (coe MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 (coe v15)))
                       (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'fold_500 v9 v10 v11 v12 v13 v18 v19 v20 v21
        -> case coe v4 of
             MAlonzo.Code.Once.Internal.Core.Syntax.C_fold_92 v22 v23 v24
               -> coe
                    MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'fold_500 v9 v10 v11
                    v12 v13 v18
                    (coe
                       MAlonzo.Code.Once.TypeCheck.RigidSubst.du_ρ'770''45'wf_42 (coe v0)
                       (coe v1) (coe v3) (coe v22) (coe v19))
                    (coe
                       du_ρ'770''7580'_840 (coe v0) (coe v1) (coe v2) (coe v3) (coe v23)
                       (coe
                          MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28
                          (coe
                             MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62 (coe v22)
                             (coe v5))
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v11))
                          (coe v5))
                       (coe v20))
                    (coe
                       du_ρ'770''7580'_840 (coe v0) (coe v1) (coe v2) (coe v3) (coe v24)
                       (coe MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 (coe v22))
                       (coe v21))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'unfold_524 v9 v10 v12 v13 v15 v18 v19 v20
        -> case coe v4 of
             MAlonzo.Code.Once.Internal.Core.Syntax.C_unfold_94 v21 v22 v23
               -> case coe v5 of
                    MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v24 v25
                      -> coe
                           MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'unfold_524 v9 v10
                           v12 v13
                           (coe
                              MAlonzo.Code.Once.TypeCheck.RigidSubst.du_ρ'770'_14 (coe v0)
                              (coe v1) (coe v2) (coe v15))
                           (coe
                              MAlonzo.Code.Once.TypeCheck.RigidSubst.du_ρ'770''45'wf_42 (coe v0)
                              (coe v1) (coe v3) (coe v21) (coe v18))
                           (coe
                              du_ρ'770''7580'_840 (coe v0) (coe v1) (coe v2) (coe v3) (coe v22)
                              (coe
                                 MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v15)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_fin_42 (coe v25)))
                                 (coe
                                    MAlonzo.Code.Once.Internal.Type.d_'10214'_'10215'T_62 (coe v21)
                                    (coe v15)))
                              (coe v19))
                           (coe
                              du_ρ'770''7580'_840 (coe v0) (coe v1) (coe v2) (coe v3) (coe v23)
                              (coe v15) (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'out_540 v10 v11 v12 v14 v15
        -> case coe v4 of
             MAlonzo.Code.Once.Internal.Core.Syntax.C_out_98 v16
               -> coe
                    MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'out_540 v10 v11
                    (coe
                       MAlonzo.Code.Once.TypeCheck.RigidSubst.du_ρ'770'F_18 (coe v0)
                       (coe v1) (coe v2) (coe v12))
                    (coe
                       MAlonzo.Code.Once.TypeCheck.RigidSubst.du_ρ'770''45'wf_42 (coe v0)
                       (coe v1) (coe v3) (coe v12) (coe v14))
                    (coe
                       du_ρ'770''7580'_840 (coe v0) (coe v1) (coe v2) (coe v3) (coe v16)
                       (coe
                          MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 (coe v12) (coe v10))
                       (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'iter_562 v9 v10 v11 v12 v13 v17 v18
        -> case coe v4 of
             MAlonzo.Code.Once.Internal.Core.Syntax.C_iter_96 v19 v20
               -> coe
                    MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'iter_562 v9 v10 v11
                    v12
                    (MAlonzo.Code.Once.Internal.Core.PolyTy.d__'10218'_'10219'_344
                       (coe v0)
                       (coe
                          MAlonzo.Code.Once.Internal.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
                          (coe v13))
                       (coe v2))
                    (coe
                       du_ρ'770''7580'_840 (coe v0) (coe v1) (coe v2) (coe v3) (coe v19)
                       (coe
                          MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 (coe v13)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                             (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38)))
                          (coe
                             MAlonzo.Code.Once.Internal.Type.C__'43'__26 (coe v5) (coe v13)))
                       (coe v17))
                    (coe
                       du_ρ'770''7580'_840 (coe v0) (coe v1) (coe v2) (coe v3) (coe v20)
                       (coe v13) (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'coerce_578 v14 v15
        -> case coe v4 of
             MAlonzo.Code.Once.Internal.Core.Syntax.C_coerce_100 v16 v17 v18
               -> coe
                    MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'coerce_578
                    (coe
                       MAlonzo.Code.Once.TypeCheck.RigidSubst.du_ρ'770''45''60''58'_60
                       (coe v0) (coe v1) (coe v2) (coe v16) (coe v5) (coe v14))
                    (coe
                       du_ρ'770''7580'_840 (coe v0) (coe v1) (coe v2) (coe v3) (coe v18)
                       (coe v16) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'lit'45'int_586
        -> coe
             MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'lit'45'int_586
      MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'lit'45'float_594
        -> coe
             MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'lit'45'float_594
      MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'prim_608 v13
        -> case coe v4 of
             MAlonzo.Code.Once.Internal.Core.Syntax.C_prim_104 v14 v15
               -> coe
                    MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'prim_608
                    (coe
                       du_ρ'770''7580'_840 (coe v0) (coe v1) (coe v2) (coe v3) (coe v15)
                       (coe
                          MAlonzo.Code.Once.Internal.Core.Syntax.du_primDom_56 (coe v14))
                       (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'sigop_620 v11 v12 v13 v14 v15
        -> coe
             MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'sigop_620 v11 v12
             v13 v14 v15
      MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'ref_630 v11
        -> case coe v4 of
             MAlonzo.Code.Once.Internal.Core.Syntax.C_ref_110 v12 v13
               -> coe
                    MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'ref_630
                    (\ v14 v15 ->
                       coe
                         MAlonzo.Code.Once.TypeCheck.RigidSubst.du_ρ'770''45'base_36
                         (coe v0) (coe v1) (coe v3) (coe v13 v14) (coe v11 v14 v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'sub'45'use_646 v9 v14 v15
        -> coe
             MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'sub'45'use_646 v9
             v14
             (coe
                du_ρ'770''7580'_840 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v15))
      MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'sub'45'eff_662 v10 v14 v15
        -> coe
             MAlonzo.Code.Once.Internal.Core.Typing.C_'8866'sub'45'eff_662 v10
             v14
             (coe
                du_ρ'770''7580'_840 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v15))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoreInst.WithSG.ρ̂ᶜ-let-pure
d_ρ'770''7580''45'let'45'pure_1052 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ρ'770''7580''45'let'45'pure_1052 = erased
-- Once.Adequacy.CoreInst.WithSG.ρ̂ᶜ-app-pure
d_ρ'770''7580''45'app'45'pure_1090 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ρ'770''7580''45'app'45'pure_1090 = erased
-- Once.Adequacy.CoreInst.WithSG.ρ̂S-abs
d_ρ'770'S'45'abs_1108 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ρ'770'S'45'abs_1108 = erased
-- Once.Adequacy.CoreInst.WithSG.IA
d_IA_1130 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_IA_1130 ~v0 ~v1 ~v2 v3 v4 v5 v6 ~v7 ~v8 ~v9 ~v10 v11 v12 ~v13 v14
  = du_IA_1130 v3 v4 v5 v6 v11 v12 v14
du_IA_1130 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8) ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_IA_1130 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Internal.Core.PolyTyping.du_instantiate_1090
      (coe v0)
      (coe
         MAlonzo.Code.Once.Internal.Core.Abstract.du_absTm_694 (coe v0)
         (coe v1) (coe v4))
      (coe
         MAlonzo.Code.Once.Internal.Core.AbsTy.d_absTy_82 (coe v0) (coe v1)
         (coe v5))
      (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Once.Internal.Core.Abstract.du_abs'45''8866'_934
         (coe v0) (coe v1) (coe v4) (coe v5) (coe v6))
-- Once.Adequacy.CoreInst.WithSG.tr-isubst′
d_tr'45'isubst'8242'_1172 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Core.PolyTyping.T_PCtx_362 ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.PolyTyping.T_PTm_402 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Core.PolyTy.T_Ty_16) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Core.PolyTyping.T__'8873'_'8866''91'_'93'_'8759'_'33'__650 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tr'45'isubst'8242'_1172 = erased
-- Once.Adequacy.CoreInst.WithSG.close
d_close_1204 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_close_1204 = erased
-- Once.Adequacy.CoreInst.WithSG.closeF
d_closeF_1238 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_closeF_1238 = erased
-- Once.Adequacy.CoreInst.WithSG.tr-var-subst
d_tr'45'var'45'subst_1260 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tr'45'var'45'subst_1260 = erased
-- Once.Adequacy.CoreInst.WithSG.inst-abs
d_inst'45'abs_1278 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inst'45'abs_1278 = erased
-- Once.Adequacy.CoreInst.WithSG._.c3
d_c3_1330 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_c3_1330 = erased
-- Once.Adequacy.CoreInst.WithSG.ρ̂ₜ-ren
d_ρ'770''8348''45'ren_1442 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ρ'770''8348''45'ren_1442 = erased
-- Once.Adequacy.CoreInst.WithSG.ρ̂θ
d_ρ'770'θ_1592 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10
d_ρ'770'θ_1592 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11 v12
  = du_ρ'770'θ_1592 v10 v11 v12
du_ρ'770'θ_1592 ::
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10
du_ρ'770'θ_1592 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Surface.Thinning.C_done_12 -> coe v2
      MAlonzo.Code.Once.Surface.Thinning.C_skip_26 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Context.C__'44'_'94'__12 v11 v12 v13
               -> coe
                    MAlonzo.Code.Once.Surface.Thinning.C_skip_26
                    (coe du_ρ'770'θ_1592 (coe v0) (coe v11) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Thinning.C_keep_40 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Context.C__'44'_'94'__12 v11 v12 v13
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Context.C__'44'_'94'__12 v15 v16 v17
                      -> coe
                           MAlonzo.Code.Once.Surface.Thinning.C_keep_40
                           (coe du_ρ'770'θ_1592 (coe v11) (coe v15) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CoreInst.WithSG.thin-var-ρ̂
d_thin'45'var'45'ρ'770'_1610 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thin'45'var'45'ρ'770'_1610 = erased
-- Once.Adequacy.CoreInst.WithSG.thin-usage-ρ̂
d_thin'45'usage'45'ρ'770'_1634 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thin'45'usage'45'ρ'770'_1634 = erased
-- Once.Adequacy.CoreInst.WithSG.ρ̂θ-refl
d_ρ'770'θ'45'refl_1654 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ρ'770'θ'45'refl_1654 = erased
-- Once.Adequacy.CoreInst.WithSG._.ρ̂ᶜ-sU
d_ρ'770''7580''45'sU_1686 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_ρ'770''7580''45'sU_1686 = erased
-- Once.Adequacy.CoreInst.WithSG._.ρ̂ᶜ-st
d_ρ'770''7580''45'st_1702 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_ρ'770''7580''45'st_1702 = erased
-- Once.Adequacy.CoreInst.WithSG._.ρ̂ᶜ-sA
d_ρ'770''7580''45'sA_1722 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_ρ'770''7580''45'sA_1722 = erased
-- Once.Adequacy.CoreInst.WithSG._.ren-sA
d_ren'45'sA_1750 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_ren'45'sA_1750 = erased
-- Once.Adequacy.CoreInst.WithSG._.ρ̂ᶜ-sUf
d_ρ'770''7580''45'sUf_1774 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  Integer ->
  (MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Internal.Context.T_Usage_46) ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_ρ'770''7580''45'sUf_1774 = erased
-- Once.Adequacy.CoreInst.WithSG._.rmUf
d_rmUf_1796 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  Integer ->
  (MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Internal.Context.T_Usage_46) ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_rmUf_1796 = erased
-- Once.Adequacy.CoreInst.WithSG._.rmU
d_rmU_1814 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_rmU_1814 = erased
-- Once.Adequacy.CoreInst.WithSG._.rmt
d_rmt_1830 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_rmt_1830 = erased
-- Once.Adequacy.CoreInst.WithSG._.rmA
d_rmA_1850 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_rmA_1850 = erased
-- Once.Adequacy.CoreInst.WithSG.rm
d_rm_1866 ::
  MAlonzo.Code.Once.Internal.Core.PolyTy.T_Sig_826 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_TKind_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Type.T_Type_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_rm_1866 = erased
-- Once.Adequacy.CoreInst.WithSG.U≡
d_U'8801'_1886 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_U'8801'_1886 = erased
-- Once.Adequacy.CoreInst.WithSG.T≡
d_T'8801'_1904 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_T'8801'_1904 = erased
-- Once.Adequacy.CoreInst.WithSG.T≡e
d_T'8801'e_1924 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_T'8801'e_1924 = erased
-- Once.Adequacy.CoreInst.WithSG._.ex
d_ex_1936 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ex_1936 = erased
-- Once.Adequacy.CoreInst.WithSG._.≅var
d_'8773'var_1952 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_'8773'var_1952 = erased
-- Once.Adequacy.CoreInst.WithSG._.≅1
d_'8773'1_1988 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  (MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Internal.Context.T_Usage_46) ->
  (MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62) ->
  (MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
   MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248) ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_'8773'1_1988 = erased
-- Once.Adequacy.CoreInst.WithSG._.≅2
d_'8773'2_2054 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  (MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Internal.Context.T_Usage_46) ->
  (MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62) ->
  (MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
   MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
   MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
   MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
   MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248) ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_'8773'2_2054 = erased
-- Once.Adequacy.CoreInst.WithSG._.≅lam
d_'8773'lam_2086 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_'8773'lam_2086 = erased
-- Once.Adequacy.CoreInst.WithSG._.≅let
d_'8773'let_2122 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_'8773'let_2122 = erased
-- Once.Adequacy.CoreInst.WithSG._.≅case
d_'8773'case_2170 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_'8773'case_2170 = erased
-- Once.Adequacy.CoreInst.WithSG._.≅case⊔
d_'8773'case'8852'_2222 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
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
d_'8773'case'8852'_2222 = erased
-- Once.Adequacy.CoreInst.WithSG._.≅sub-use
d_'8773'sub'45'use_2248 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Internal.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_'8773'sub'45'use_2248 = erased
-- Once.Adequacy.CoreInst.WithSG._._.irr
d_irr_2260 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Internal.Context.T__'8849''7512'__178 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_irr_2260 = erased
-- Once.Adequacy.CoreInst.WithSG.ρ̂ᶜ-ren
d_ρ'770''7580''45'ren_2282 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_ρ'770''7580''45'ren_2282 = erased
-- Once.Adequacy.CoreInst.WithSG.ren-θ≡
d_ren'45'θ'8801'_2644 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_ren'45'θ'8801'_2644 = erased
-- Once.Adequacy.CoreInst.WithSG.wk≅
d_wk'8773'_2664 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_wk'8773'_2664 = erased
-- Once.Adequacy.CoreInst.WithSG.ρ̂θ-∅
d_ρ'770'θ'45''8709'_2688 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ρ'770'θ'45''8709'_2688 = erased
-- Once.Adequacy.CoreInst.WithSG.close≅
d_close'8773'_2708 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_close'8773'_2708 = erased
-- Once.Adequacy.CoreInst.WithSG._.c-compose
d_c'45'compose_2750 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_c'45'compose_2750 = erased
-- Once.Adequacy.CoreInst.WithSG._.c-pair
d_c'45'pair_2806 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_c'45'pair_2806 = erased
-- Once.Adequacy.CoreInst.WithSG._._.E
d_E_2830 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_E_2830 = erased
-- Once.Adequacy.CoreInst.WithSG._.c-case
d_c'45'case_2856 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_c'45'case_2856 = erased
-- Once.Adequacy.CoreInst.WithSG._._.E
d_E_2880 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_E_2880 = erased
-- Once.Adequacy.CoreInst.WithSG._.c-curry
d_c'45'curry_2906 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_c'45'curry_2906 = erased
-- Once.Adequacy.CoreInst.WithSG._._.E
d_E_2918 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_E_2918 = erased
-- Once.Adequacy.CoreInst.WithSG._.c-apply
d_c'45'apply_2928 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_c'45'apply_2928 = erased
-- Once.Adequacy.CoreInst.WithSG._.c-applyEff
d_c'45'applyEff_2936 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_c'45'applyEff_2936 = erased
-- Once.Adequacy.CoreInst.WithSG._.c-effApp
d_c'45'effApp_2956 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_c'45'effApp_2956 = erased
-- Once.Adequacy.CoreInst.WithSG._.in-gen
d_in'45'gen_2988 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_in'45'gen_2988 = erased
-- Once.Adequacy.CoreInst.WithSG._.out-gen
d_out'45'gen_3006 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_out'45'gen_3006 = erased
-- Once.Adequacy.CoreInst.WithSG._.outEff-gen
d_outEff'45'gen_3026 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_outEff'45'gen_3026 = erased
-- Once.Adequacy.CoreInst.WithSG._.c-in
d_c'45'in_3034 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_c'45'in_3034 = erased
-- Once.Adequacy.CoreInst.WithSG._.c-out
d_c'45'out_3044 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_c'45'out_3044 = erased
-- Once.Adequacy.CoreInst.WithSG._.c-outEff
d_c'45'outEff_3056 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_c'45'outEff_3056 = erased
-- Once.Adequacy.CoreInst.WithSG._.cata-gen
d_cata'45'gen_3092 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_cata'45'gen_3092 = erased
-- Once.Adequacy.CoreInst.WithSG._.ana-gen
d_ana'45'gen_3126 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_ana'45'gen_3126 = erased
-- Once.Adequacy.CoreInst.WithSG._.c-cata
d_c'45'cata_3150 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_c'45'cata_3150 = erased
-- Once.Adequacy.CoreInst.WithSG._._.E
d_E_3168 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_E_3168 = erased
-- Once.Adequacy.CoreInst.WithSG._.c-loop
d_c'45'loop_3184 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_c'45'loop_3184 = erased
-- Once.Adequacy.CoreInst.WithSG._._.E
d_E_3194 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_E_3194 = erased
-- Once.Adequacy.CoreInst.WithSG._.c-ana
d_c'45'ana_3220 ::
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
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Internal.Core.AbsTy.T_ConstFree_374) ->
  Integer ->
  MAlonzo.Code.Once.Internal.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Internal.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
  MAlonzo.Code.Once.Internal.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_c'45'ana_3220 = erased
