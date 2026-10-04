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

module MAlonzo.Code.Once.Spec.Core.Rename where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Spec.Core.PolyTy
import qualified MAlonzo.Code.Once.Spec.Core.Syntax
import qualified MAlonzo.Code.Once.Spec.Core.Typing
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Thinning
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.Type.Sub

-- Once.Spec.Core.Rename._.Tm
d_Tm_26 a0 a1 a2 a3 = ()
-- Once.Spec.Core.Rename._.extR
d_extR_38 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
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
  = coe MAlonzo.Code.Once.Spec.Core.Syntax.du_extR_120 v2 v3
-- Once.Spec.Core.Rename._.ren
d_ren_106 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_ren_106 ~v0 ~v1 ~v2 = du_ren_106
du_ren_106 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_ren_106 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Spec.Core.Syntax.du_ren_132 v2 v3
-- Once.Spec.Core.Rename._.wk
d_wk_138 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_wk_138 ~v0 ~v1 ~v2 = du_wk_138
du_wk_138 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_wk_138 v0 = coe MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_242
-- Once.Spec.Core.Rename._._⊢[_]_∷_!_
d__'8866''91'_'93'_'8759'_'33'__244 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.Spec.Core.Rename.ren-cong
d_ren'45'cong_352 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ren'45'cong_352 = erased
-- Once.Spec.Core.Rename._.extR-cong
d_extR'45'cong_378 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
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
d_extR'45'cong_378 = erased
-- Once.Spec.Core.Rename._.ext
d_ext_410 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext_410 = erased
-- Once.Spec.Core.Rename._.ext
d_ext_462 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ext_462 = erased
-- Once.Spec.Core.Rename.keep-extR
d_keep'45'extR_544 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_keep'45'extR_544 = erased
-- Once.Spec.Core.Rename.ren-⊢
d_ren'45''8866'_570 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_ren'45''8866'_570 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 v8 v9 v10 v11 v12
  = du_ren'45''8866'_570 v5 v6 v8 v9 v10 v11 v12
du_ren'45''8866'_570 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_ren'45''8866'_570 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252
        -> coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272 v11 v17
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_lam_68 v18
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v19 v20 v21
                      -> case coe v20 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v22 v23
                             -> coe
                                  MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272 v11
                                  (coe
                                     du_ren'45''8866'_570
                                     (coe
                                        MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v0 v19
                                        (coe MAlonzo.Code.Once.Type.C_Many_10))
                                     (coe
                                        MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v1 v19
                                        (coe MAlonzo.Code.Once.Type.C_Many_10))
                                     (coe v18) (coe v21) (coe v23)
                                     (coe MAlonzo.Code.Once.Surface.Thinning.C_keep_40 v5)
                                     (coe v17))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'app_294 v9 v10 v11 v13 v17 v18
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_app_70 v19 v20
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'app_294
                    (coe
                       MAlonzo.Code.Once.Surface.Thinning.du_thin'45'usage_138 (coe v0)
                       (coe v1) (coe v5) (coe v9))
                    (coe
                       MAlonzo.Code.Once.Surface.Thinning.du_thin'45'usage_138 (coe v0)
                       (coe v1) (coe v5) (coe v10))
                    v11 v13
                    (coe
                       du_ren'45''8866'_570 (coe v0) (coe v1) (coe v19)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v13)
                          (coe MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v11) (coe v4))
                          (coe v3))
                       (coe v4) (coe v5) (coe v17))
                    (coe
                       du_ren'45''8866'_570 (coe v0) (coe v1) (coe v20) (coe v13) (coe v4)
                       (coe v5) (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'let_316 v9 v10 v11 v13 v17 v18
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_let'8242'_72 v19 v20
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'let_316
                    (coe
                       MAlonzo.Code.Once.Surface.Thinning.du_thin'45'usage_138 (coe v0)
                       (coe v1) (coe v5) (coe v9))
                    (coe
                       MAlonzo.Code.Once.Surface.Thinning.du_thin'45'usage_138 (coe v0)
                       (coe v1) (coe v5) (coe v10))
                    v11 v13
                    (coe
                       du_ren'45''8866'_570 (coe v0) (coe v1) (coe v19) (coe v13) (coe v4)
                       (coe v5) (coe v17))
                    (coe
                       du_ren'45''8866'_570
                       (coe
                          MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v0 v13
                          (coe MAlonzo.Code.Once.Type.C_Many_10))
                       (coe
                          MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v1 v13
                          (coe MAlonzo.Code.Once.Type.C_Many_10))
                       (coe v20) (coe v3) (coe v4)
                       (coe MAlonzo.Code.Once.Surface.Thinning.C_keep_40 v5) (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'unit_322
        -> coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'unit_322
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'pair_342 v9 v10 v16 v17
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_pair_76 v18 v19
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'42'__124 v20 v21
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'pair_342
                           (coe
                              MAlonzo.Code.Once.Surface.Thinning.du_thin'45'usage_138 (coe v0)
                              (coe v1) (coe v5) (coe v9))
                           (coe
                              MAlonzo.Code.Once.Surface.Thinning.du_thin'45'usage_138 (coe v0)
                              (coe v1) (coe v5) (coe v10))
                           (coe
                              du_ren'45''8866'_570 (coe v0) (coe v1) (coe v18) (coe v20) (coe v4)
                              (coe v5) (coe v16))
                           (coe
                              du_ren'45''8866'_570 (coe v0) (coe v1) (coe v19) (coe v21) (coe v4)
                              (coe v5) (coe v17))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'fst_358 v12 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_fst_78 v15
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'fst_358 v12
                    (coe
                       du_ren'45''8866'_570 (coe v0) (coe v1) (coe v15)
                       (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v3) (coe v12))
                       (coe v4) (coe v5) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'snd_374 v11 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_snd_80 v15
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'snd_374 v11
                    (coe
                       du_ren'45''8866'_570 (coe v0) (coe v1) (coe v15)
                       (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v11) (coe v3))
                       (coe v4) (coe v5) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'inl_390 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_inl_82 v15
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'43'__126 v16 v17
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'inl_390
                           (coe
                              du_ren'45''8866'_570 (coe v0) (coe v1) (coe v15) (coe v16) (coe v4)
                              (coe v5) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'inr_406 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_inr_84 v15
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'43'__126 v16 v17
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'inr_406
                           (coe
                              du_ren'45''8866'_570 (coe v0) (coe v1) (coe v15) (coe v17) (coe v4)
                              (coe v5) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'case_436 v9 v10 v11 v12 v13 v15 v16 v21 v22 v23
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_case_86 v24 v25 v26
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'case_436
                    (coe
                       MAlonzo.Code.Once.Surface.Thinning.du_thin'45'usage_138 (coe v0)
                       (coe v1) (coe v5) (coe v9))
                    (coe
                       MAlonzo.Code.Once.Surface.Thinning.du_thin'45'usage_138 (coe v0)
                       (coe v1) (coe v5) (coe v10))
                    (coe
                       MAlonzo.Code.Once.Surface.Thinning.du_thin'45'usage_138 (coe v0)
                       (coe v1) (coe v5) (coe v11))
                    v12 v13 v15 v16
                    (coe
                       du_ren'45''8866'_570 (coe v0) (coe v1) (coe v24)
                       (coe MAlonzo.Code.Once.Type.C__'43'__126 (coe v15) (coe v16))
                       (coe v4) (coe v5) (coe v21))
                    (coe
                       du_ren'45''8866'_570
                       (coe
                          MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v0 v15
                          (coe MAlonzo.Code.Once.Type.C_Many_10))
                       (coe
                          MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v1 v15
                          (coe MAlonzo.Code.Once.Type.C_Many_10))
                       (coe v25) (coe v3) (coe v4)
                       (coe MAlonzo.Code.Once.Surface.Thinning.C_keep_40 v5) (coe v22))
                    (coe
                       du_ren'45''8866'_570
                       (coe
                          MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v0 v16
                          (coe MAlonzo.Code.Once.Type.C_Many_10))
                       (coe
                          MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v1 v16
                          (coe MAlonzo.Code.Once.Type.C_Many_10))
                       (coe v26) (coe v3) (coe v4)
                       (coe MAlonzo.Code.Once.Surface.Thinning.C_keep_40 v5) (coe v23))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'absurd_450 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_absurd_88 v14
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'absurd_450
                    (coe
                       du_ren'45''8866'_570 (coe v0) (coe v1) (coe v14)
                       (coe MAlonzo.Code.Once.Type.C_Void_122) (coe v4) (coe v5)
                       (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'roll_464 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_roll_90 v15
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_130 v16
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'roll_464 v13
                           (coe
                              du_ren'45''8866'_570 (coe v0) (coe v1) (coe v15)
                              (coe
                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v16) (coe v3))
                              (coe v4) (coe v5) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'fold_484 v9 v10 v12 v16 v17 v18
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_fold_92 v19 v20
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'fold_484
                    (coe
                       MAlonzo.Code.Once.Surface.Thinning.du_thin'45'usage_138 (coe v0)
                       (coe v1) (coe v5) (coe v9))
                    (coe
                       MAlonzo.Code.Once.Surface.Thinning.du_thin'45'usage_138 (coe v0)
                       (coe v1) (coe v5) (coe v10))
                    v12 v16
                    (coe
                       du_ren'45''8866'_570 (coe v0) (coe v1) (coe v19)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                          (coe
                             MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v12) (coe v3))
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v4))
                          (coe v3))
                       (coe v4) (coe v5) (coe v17))
                    (coe
                       du_ren'45''8866'_570 (coe v0) (coe v1) (coe v20)
                       (coe MAlonzo.Code.Once.Type.C_μ'45'type_130 (coe v12)) (coe v4)
                       (coe v5) (coe v18))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'unfold_506 v9 v10 v14 v17 v18 v19
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_unfold_94 v20 v21
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C_ν'45'type_132 v22 v23
                      -> coe
                           MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'unfold_506
                           (coe
                              MAlonzo.Code.Once.Surface.Thinning.du_thin'45'usage_138 (coe v0)
                              (coe v1) (coe v5) (coe v9))
                           (coe
                              MAlonzo.Code.Once.Surface.Thinning.du_thin'45'usage_138 (coe v0)
                              (coe v1) (coe v5) (coe v10))
                           v14 v17
                           (coe
                              du_ren'45''8866'_570 (coe v0) (coe v1) (coe v20)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v14)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v23))
                                 (coe
                                    MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v22)
                                    (coe v14)))
                              (coe v4) (coe v5) (coe v18))
                           (coe
                              du_ren'45''8866'_570 (coe v0) (coe v1) (coe v21) (coe v14) (coe v4)
                              (coe v5) (coe v19))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'out_520 v11 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_out_96 v15
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'out_520 v11 v13
                    (coe
                       du_ren'45''8866'_570 (coe v0) (coe v1) (coe v15)
                       (coe MAlonzo.Code.Once.Type.C_ν'45'type_132 (coe v11) (coe v4))
                       (coe v4) (coe v5) (coe v14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'coerce_536 v14 v15
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_coerce_98 v16 v17 v18
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'coerce_536 v14
                    (coe
                       du_ren'45''8866'_570 (coe v0) (coe v1) (coe v18) (coe v16) (coe v4)
                       (coe v5) (coe v15))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lit'45'int_544
        -> coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lit'45'int_544
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lit'45'float_552
        -> coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lit'45'float_552
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'prim_566 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Core.Syntax.C_prim_102 v14 v15
               -> coe
                    MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'prim_566
                    (coe
                       du_ren'45''8866'_570 (coe v0) (coe v1) (coe v15)
                       (coe MAlonzo.Code.Once.Spec.Core.Syntax.du_primDom_56 (coe v14))
                       (coe v4) (coe v5) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sigop_578 v11 v12 v13 v14
        -> coe
             MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sigop_578 v11 v12 v13
             v14
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'ref_588 v11
        -> coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'ref_588 v11
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_604 v10 v14 v15
        -> coe
             MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_604 v10 v14
             (coe
                du_ren'45''8866'_570 (coe v0) (coe v1) (coe v2) (coe v3) (coe v10)
                (coe v5) (coe v15))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Rename.thin-var-refl
d_thin'45'var'45'refl_858 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_thin'45'var'45'refl_858 = erased
-- Once.Spec.Core.Rename.wk-⊢
d_wk'45''8866'_880 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_wk'45''8866'_880 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 v8 v9 v10
  = du_wk'45''8866'_880 v4 v6 v7 v8 v9 v10
du_wk'45''8866'_880 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_wk'45''8866'_880 v0 v1 v2 v3 v4 v5
  = coe
      du_ren'45''8866'_570 (coe v0)
      (coe
         MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v0 v4
         (coe MAlonzo.Code.Once.Type.C_Many_10))
      (coe v1) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Once.Surface.Thinning.du_'8838''45'wk_58 (coe v0))
      (coe v5)
-- Once.Spec.Core.Rename.∅⊆
d_'8709''8838'_898 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10
d_'8709''8838'_898 ~v0 ~v1 ~v2 ~v3 v4 = du_'8709''8838'_898 v4
du_'8709''8838'_898 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Thinning.T__'8838'__10
du_'8709''8838'_898 v0
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Context.C_'8709'_8
        -> coe MAlonzo.Code.Once.Surface.Thinning.C_done_12
      MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Surface.Thinning.C_skip_26
             (coe du_'8709''8838'_898 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Core.Rename.close
d_close_904 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_close_904 ~v0 ~v1 ~v2 ~v3 = du_close_904
du_close_904 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_close_904
  = coe MAlonzo.Code.Once.Spec.Core.Syntax.du_ren_132 erased
-- Once.Spec.Core.Rename.⊢close
d_'8866'close_916 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'close_916 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_'8866'close_916 v4 v5 v6 v7 v8
du_'8866'close_916 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'close_916 v0 v1 v2 v3 v4
  = coe
      du_ren'45''8866'_570
      (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8) (coe v0)
      (coe v1) (coe v2) (coe v3) (coe du_'8709''8838'_898 (coe v0))
      (coe v4)
