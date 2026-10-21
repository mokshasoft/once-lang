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

module MAlonzo.Code.Once.Lang.Core.Rename where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Core.PolyTy
import qualified MAlonzo.Code.Once.Lang.Core.Syntax
import qualified MAlonzo.Code.Once.Lang.Core.Typing
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Sub
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Surface.Thinning

-- Once.Lang.Core.Rename._.Tm
d_Tm_26 a0 a1 a2 a3 = ()
-- Once.Lang.Core.Rename._.extR
d_extR_38 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_extR_38 ~v0 ~v1 ~v2 = du_extR_38
du_extR_38 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_extR_38 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Core.Syntax.du_extR_122 v2 v3
-- Once.Lang.Core.Rename._.ren
d_ren_108 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_ren_108 ~v0 ~v1 ~v2 = du_ren_108
du_ren_108 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_ren_108 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Core.Syntax.du_ren_134 v2 v3
-- Once.Lang.Core.Rename._.wk
d_wk_140 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_wk_140 ~v0 ~v1 ~v2 = du_wk_140
du_wk_140 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_wk_140 v0 = coe MAlonzo.Code.Once.Lang.Core.Syntax.du_wk_274
-- Once.Lang.Core.Rename._._⊢[_]_∷_!_
d__'8866''91'_'93'_'8759'_'33'__248 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.Lang.Core.Rename.ren-cong
d_ren'45'cong_372 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'cong_372 = erased
-- Once.Lang.Core.Rename._.extR-cong
d_extR'45'cong_404 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extR'45'cong_404 = erased
-- Once.Lang.Core.Rename._.ext
d_ext_438 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext_438 = erased
-- Once.Lang.Core.Rename._.ext
d_ext_498 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext_498 = erased
-- Once.Lang.Core.Rename.keep-extR
d_keep'45'extR_594 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'extR_594 = erased
-- Once.Lang.Core.Rename.ren-⊢
d_ren'45''8866'_620 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_ren'45''8866'_620 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 ~v10 v11 v12
  = du_ren'45''8866'_620 v5 v6 v7 v8 v9 v11 v12
du_ren'45''8866'_620 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_ren'45''8866'_620 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256
        -> coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276 v11 v17
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_lam_68 v18 v19 v20 v21
               -> case coe v4 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v22 v23 v24
                      -> coe
                           MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276 v11
                           (coe
                              du_ren'45''8866'_620
                              (coe
                                 MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v0 v18
                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                              (coe
                                 MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v1 v18
                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                              (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v11 v2) (coe v21)
                              (coe v24) (coe MAlonzo.Code.Once.Surface.Thinning.C_keep_40 v5)
                              (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'app_302 v9 v10 v11 v12 v13 v14 v15 v19 v20
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_app_70 v21 v22
               -> coe
                    MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'app_302
                    (coe
                       MAlonzo.Code.Once.Surface.Thinning.du_thin'45'usage_112 (coe v0)
                       (coe v1) (coe v5) (coe v9))
                    (coe
                       MAlonzo.Code.Once.Surface.Thinning.du_thin'45'usage_112 (coe v0)
                       (coe v1) (coe v5) (coe v10))
                    v11 v12 v13 v14 v15
                    (coe
                       du_ren'45''8866'_620 (coe v0) (coe v1) (coe v9) (coe v21)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v15)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78 (coe v11)
                             (coe v12))
                          (coe v4))
                       (coe v5) (coe v19))
                    (coe
                       du_ren'45''8866'_620 (coe v0) (coe v1) (coe v10) (coe v22)
                       (coe v15) (coe v5) (coe v20))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'let_326 v9 v10 v12 v13 v14 v18 v19
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_let'8242'_72 v20 v21 v22
               -> coe
                    MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'let_326
                    (coe
                       MAlonzo.Code.Once.Surface.Thinning.du_thin'45'usage_112 (coe v0)
                       (coe v1) (coe v5) (coe v9))
                    (coe
                       MAlonzo.Code.Once.Surface.Thinning.du_thin'45'usage_112 (coe v0)
                       (coe v1) (coe v5) (coe v10))
                    v12 v13 v14
                    (coe
                       du_ren'45''8866'_620 (coe v0) (coe v1) (coe v9) (coe v21) (coe v14)
                       (coe v5) (coe v18))
                    (coe
                       du_ren'45''8866'_620
                       (coe
                          MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v0 v14
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                       (coe
                          MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v1 v14
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                       (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v20 v10)
                       (coe v22) (coe v4)
                       (coe MAlonzo.Code.Once.Surface.Thinning.C_keep_40 v5) (coe v19))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'unit_332
        -> coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'unit_332
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'pair_354 v9 v10 v11 v12 v17 v18
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_pair_76 v19 v20
               -> case coe v4 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v21 v22
                      -> coe
                           MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'pair_354
                           (coe
                              MAlonzo.Code.Once.Surface.Thinning.du_thin'45'usage_112 (coe v0)
                              (coe v1) (coe v5) (coe v9))
                           (coe
                              MAlonzo.Code.Once.Surface.Thinning.du_thin'45'usage_112 (coe v0)
                              (coe v1) (coe v5) (coe v10))
                           v11 v12
                           (coe
                              du_ren'45''8866'_620 (coe v0) (coe v1) (coe v9) (coe v19) (coe v21)
                              (coe v5) (coe v17))
                           (coe
                              du_ren'45''8866'_620 (coe v0) (coe v1) (coe v10) (coe v20)
                              (coe v22) (coe v5) (coe v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'fst_370 v12 v14
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_fst_78 v15
               -> coe
                    MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'fst_370 v12
                    (coe
                       du_ren'45''8866'_620 (coe v0) (coe v1) (coe v2) (coe v15)
                       (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v4) (coe v12))
                       (coe v5) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'snd_386 v11 v14
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_snd_80 v15
               -> coe
                    MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'snd_386 v11
                    (coe
                       du_ren'45''8866'_620 (coe v0) (coe v1) (coe v2) (coe v15)
                       (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v11) (coe v4))
                       (coe v5) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'inl_402 v14
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_inl_82 v15 v16
               -> case coe v4 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v17 v18
                      -> coe
                           MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'inl_402
                           (coe
                              du_ren'45''8866'_620 (coe v0) (coe v1) (coe v2) (coe v16) (coe v17)
                              (coe v5) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'inr_418 v14
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_inr_84 v15 v16
               -> case coe v4 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v17 v18
                      -> coe
                           MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'inr_418
                           (coe
                              du_ren'45''8866'_620 (coe v0) (coe v1) (coe v2) (coe v16) (coe v18)
                              (coe v5) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'case_448 v9 v10 v13 v14 v15 v16 v21 v22 v23
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_case_86 v24 v25 v26 v27 v28
               -> coe
                    MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'case_448
                    (coe
                       MAlonzo.Code.Once.Surface.Thinning.du_thin'45'usage_112 (coe v0)
                       (coe v1) (coe v5) (coe v9))
                    (coe
                       MAlonzo.Code.Once.Surface.Thinning.du_thin'45'usage_112 (coe v0)
                       (coe v1) (coe v5) (coe v10))
                    v13 v14 v15 v16
                    (coe
                       du_ren'45''8866'_620 (coe v0) (coe v1) (coe v9) (coe v26)
                       (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v15) (coe v16))
                       (coe v5) (coe v21))
                    (coe
                       du_ren'45''8866'_620
                       (coe
                          MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v0 v15
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                       (coe
                          MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v1 v15
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                       (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v24 v10)
                       (coe v27) (coe v4)
                       (coe MAlonzo.Code.Once.Surface.Thinning.C_keep_40 v5) (coe v22))
                    (coe
                       du_ren'45''8866'_620
                       (coe
                          MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v0 v16
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                       (coe
                          MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v1 v16
                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                       (coe MAlonzo.Code.Once.Lang.Context.C__'8759'__52 v25 v10)
                       (coe v28) (coe v4)
                       (coe MAlonzo.Code.Once.Surface.Thinning.C_keep_40 v5) (coe v23))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'absurd_462 v13
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_absurd_88 v14 v15
               -> coe
                    MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'absurd_462
                    (coe
                       du_ren'45''8866'_620 (coe v0) (coe v1) (coe v2) (coe v15)
                       (coe MAlonzo.Code.Once.Lang.Type.C_Void_22) (coe v5) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'roll_476 v13 v14
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_roll_90 v15 v16
               -> coe
                    MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'roll_476 v13
                    (coe
                       du_ren'45''8866'_620 (coe v0) (coe v1) (coe v2) (coe v16)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v15)
                          (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v15)))
                       (coe v5) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'fold_500 v9 v10 v11 v12 v13 v18 v19 v20 v21
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_fold_92 v22 v23 v24
               -> coe
                    MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'fold_500
                    (coe
                       MAlonzo.Code.Once.Surface.Thinning.du_thin'45'usage_112 (coe v0)
                       (coe v1) (coe v5) (coe v9))
                    (coe
                       MAlonzo.Code.Once.Surface.Thinning.du_thin'45'usage_112 (coe v0)
                       (coe v1) (coe v5) (coe v10))
                    v11 v12 v13 v18 v19
                    (coe
                       du_ren'45''8866'_620 (coe v0) (coe v1) (coe v9) (coe v23)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                          (coe
                             MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v22)
                             (coe v4))
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v11))
                          (coe v4))
                       (coe v5) (coe v20))
                    (coe
                       du_ren'45''8866'_620 (coe v0) (coe v1) (coe v10) (coe v24)
                       (coe MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 (coe v22)) (coe v5)
                       (coe v21))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'unfold_524 v9 v10 v12 v13 v15 v18 v19 v20
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_unfold_94 v21 v22 v23
               -> case coe v4 of
                    MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v24 v25
                      -> coe
                           MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'unfold_524
                           (coe
                              MAlonzo.Code.Once.Surface.Thinning.du_thin'45'usage_112 (coe v0)
                              (coe v1) (coe v5) (coe v9))
                           (coe
                              MAlonzo.Code.Once.Surface.Thinning.du_thin'45'usage_112 (coe v0)
                              (coe v1) (coe v5) (coe v10))
                           v12 v13 v15 v18
                           (coe
                              du_ren'45''8866'_620 (coe v0) (coe v1) (coe v9) (coe v22)
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v15)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                                    (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                    (coe MAlonzo.Code.Once.Lang.Type.Grade.d_fin_46 (coe v25)))
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v21)
                                    (coe v15)))
                              (coe v5) (coe v19))
                           (coe
                              du_ren'45''8866'_620 (coe v0) (coe v1) (coe v10) (coe v23)
                              (coe v15) (coe v5) (coe v20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'out_540 v10 v11 v12 v14 v15
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_out_98 v16
               -> coe
                    MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'out_540 v10 v11 v12 v14
                    (coe
                       du_ren'45''8866'_620 (coe v0) (coe v1) (coe v2) (coe v16)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v12) (coe v10))
                       (coe v5) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'iter_562 v9 v10 v11 v12 v13 v17 v18
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_iter_96 v19 v20
               -> coe
                    MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'iter_562
                    (coe
                       MAlonzo.Code.Once.Surface.Thinning.du_thin'45'usage_112 (coe v0)
                       (coe v1) (coe v5) (coe v9))
                    (coe
                       MAlonzo.Code.Once.Surface.Thinning.du_thin'45'usage_112 (coe v0)
                       (coe v1) (coe v5) (coe v10))
                    v11 v12 v13
                    (coe
                       du_ren'45''8866'_620 (coe v0) (coe v1) (coe v9) (coe v19)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v13)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
                          (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v4) (coe v13)))
                       (coe v5) (coe v17))
                    (coe
                       du_ren'45''8866'_620 (coe v0) (coe v1) (coe v10) (coe v20)
                       (coe v13) (coe v5) (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'coerce_578 v14 v15
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_coerce_100 v16 v17 v18
               -> coe
                    MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'coerce_578 v14
                    (coe
                       du_ren'45''8866'_620 (coe v0) (coe v1) (coe v2) (coe v18) (coe v16)
                       (coe v5) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lit'45'int_586
        -> coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lit'45'int_586
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lit'45'float_594
        -> coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lit'45'float_594
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'prim_608 v13
        -> case coe v3 of
             MAlonzo.Code.Once.Lang.Core.Syntax.C_prim_104 v14 v15
               -> coe
                    MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'prim_608
                    (coe
                       du_ren'45''8866'_620 (coe v0) (coe v1) (coe v2) (coe v15)
                       (coe MAlonzo.Code.Once.Lang.Core.Syntax.du_primDom_56 (coe v14))
                       (coe v5) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sigop_620 v11 v12 v13 v14 v15
        -> coe
             MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sigop_620 v11 v12 v13
             v14 v15
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'ref_630 v11
        -> coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'ref_630 v11
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'use_646 v9 v14 v15
        -> coe
             MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'use_646
             (coe
                MAlonzo.Code.Once.Surface.Thinning.du_thin'45'usage_112 (coe v0)
                (coe v1) (coe v5) (coe v9))
             (coe
                MAlonzo.Code.Once.Surface.Thinning.du_thin'45'usage'45''8849''7512'_272
                (coe v0) (coe v1) (coe v5) (coe v9) (coe v2) (coe v14))
             (coe
                du_ren'45''8866'_620 (coe v0) (coe v1) (coe v9) (coe v3) (coe v4)
                (coe v5) (coe v15))
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_662 v10 v14 v15
        -> coe
             MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_662 v10 v14
             (coe
                du_ren'45''8866'_620 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                (coe v5) (coe v15))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.Rename.thin-var-refl
d_thin'45'var'45'refl_942 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thin'45'var'45'refl_942 = erased
-- Once.Lang.Core.Rename.wk-⊢
d_wk'45''8866'_964 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_wk'45''8866'_964 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9 v10
  = du_wk'45''8866'_964 v4 v5 v6 v7 v9 v10
du_wk'45''8866'_964 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_wk'45''8866'_964 v0 v1 v2 v3 v4 v5
  = coe
      du_ren'45''8866'_620 (coe v0)
      (coe
         MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v0 v4
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
      (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Once.Surface.Thinning.du_'8838''45'wk_58 (coe v0))
      (coe v5)
-- Once.Lang.Core.Rename.∅⊆
d_'8709''8838'_982 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10
d_'8709''8838'_982 ~v0 ~v1 ~v2 ~v3 v4 = du_'8709''8838'_982 v4
du_'8709''8838'_982 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10
du_'8709''8838'_982 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Context.C_'8709'_8
        -> coe MAlonzo.Code.Once.Surface.Thinning.C_done_12
      MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Surface.Thinning.C_skip_26
             (coe du_'8709''8838'_982 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Core.Rename.close
d_close_988 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_close_988 ~v0 ~v1 ~v2 ~v3 = du_close_988
du_close_988 ::
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_close_988
  = coe MAlonzo.Code.Once.Lang.Core.Syntax.du_ren_134 erased
-- Once.Lang.Core.Rename.⊢close
d_'8866'close_1000 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'close_1000 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 ~v7 v8
  = du_'8866'close_1000 v4 v5 v6 v8
du_'8866'close_1000 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'close_1000 v0 v1 v2 v3
  = coe
      du_ren'45''8866'_620
      (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8) (coe v0)
      (coe
         MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe (0 :: Integer)))
      (coe v1) (coe v2) (coe du_'8709''8838'_982 (coe v0)) (coe v3)
