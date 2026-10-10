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

module MAlonzo.Code.Once.Spec.Core.DerivedTyping where

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
import qualified MAlonzo.Code.Once.Spec.Core.Derived
import qualified MAlonzo.Code.Once.Spec.Core.PolyTy
import qualified MAlonzo.Code.Once.Spec.Core.Rename
import qualified MAlonzo.Code.Once.Spec.Core.Syntax
import qualified MAlonzo.Code.Once.Spec.Core.Typing
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.Type.Sub

-- Once.Spec.Core.DerivedTyping._.Tm
d_Tm_30 a0 a1 a2 a3 = ()
-- Once.Spec.Core.DerivedTyping._.wk
d_wk_142 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_wk_142 ~v0 ~v1 ~v2 = du_wk_142
du_wk_142 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_wk_142 v0 = coe MAlonzo.Code.Once.Spec.Core.Syntax.du_wk_242
-- Once.Spec.Core.DerivedTyping._._⊢[_]_∷_!_
d__'8866''91'_'93'_'8759'_'33'__248 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.Spec.Core.DerivedTyping._.anaᶜ
d_ana'7580'_354 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_ana'7580'_354 ~v0 ~v1 ~v2 = du_ana'7580'_354
du_ana'7580'_354 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_ana'7580'_354 v0 v1
  = coe MAlonzo.Code.Once.Spec.Core.Derived.du_ana'7580'_334 v1
-- Once.Spec.Core.DerivedTyping._.applyEffᶜ
d_applyEff'7580'_356 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_applyEff'7580'_356 ~v0 ~v1 ~v2 = du_applyEff'7580'_356
du_applyEff'7580'_356 ::
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_applyEff'7580'_356 v0
  = coe MAlonzo.Code.Once.Spec.Core.Derived.du_applyEff'7580'_358
-- Once.Spec.Core.DerivedTyping._.applyᶜ
d_apply'7580'_358 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_apply'7580'_358 ~v0 ~v1 ~v2 = du_apply'7580'_358
du_apply'7580'_358 ::
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_apply'7580'_358 v0
  = coe MAlonzo.Code.Once.Spec.Core.Derived.du_apply'7580'_288
-- Once.Spec.Core.DerivedTyping._.caseᶜ
d_case'7580'_360 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_case'7580'_360 ~v0 ~v1 ~v2 = du_case'7580'_360
du_case'7580'_360 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_case'7580'_360 v0 v1 v2
  = coe MAlonzo.Code.Once.Spec.Core.Derived.du_case'7580'_316 v1 v2
-- Once.Spec.Core.DerivedTyping._.cataᶜ
d_cata'7580'_362 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_cata'7580'_362 ~v0 ~v1 ~v2 = du_cata'7580'_362
du_cata'7580'_362 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_cata'7580'_362 v0 v1
  = coe MAlonzo.Code.Once.Spec.Core.Derived.du_cata'7580'_330 v1
-- Once.Spec.Core.DerivedTyping._.composeᶜ
d_compose'7580'_364 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_compose'7580'_364 ~v0 ~v1 ~v2 = du_compose'7580'_364
du_compose'7580'_364 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_compose'7580'_364 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Core.Derived.du_compose'7580'_300 v1 v2
-- Once.Spec.Core.DerivedTyping._.effAppᶜ
d_effApp'7580'_368 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_effApp'7580'_368 ~v0 ~v1 ~v2 = du_effApp'7580'_368
du_effApp'7580'_368 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_effApp'7580'_368 v0 v1 v2
  = coe MAlonzo.Code.Once.Spec.Core.Derived.du_effApp'7580'_342 v1 v2
-- Once.Spec.Core.DerivedTyping._.fstᶜ
d_fst'7580'_370 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_fst'7580'_370 ~v0 ~v1 ~v2 = du_fst'7580'_370
du_fst'7580'_370 ::
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_fst'7580'_370 v0
  = coe MAlonzo.Code.Once.Spec.Core.Derived.du_fst'7580'_264
-- Once.Spec.Core.DerivedTyping._.idᶜ
d_id'7580'_372 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_id'7580'_372 ~v0 ~v1 ~v2 = du_id'7580'_372
du_id'7580'_372 ::
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_id'7580'_372 v0
  = coe MAlonzo.Code.Once.Spec.Core.Derived.du_id'7580'_260
-- Once.Spec.Core.DerivedTyping._.initialᶜ
d_initial'7580'_374 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_initial'7580'_374 ~v0 ~v1 ~v2 = du_initial'7580'_374
du_initial'7580'_374 ::
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_initial'7580'_374 v0
  = coe MAlonzo.Code.Once.Spec.Core.Derived.du_initial'7580'_284
-- Once.Spec.Core.DerivedTyping._.inlᶜ
d_inl'7580'_376 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_inl'7580'_376 ~v0 ~v1 ~v2 = du_inl'7580'_376
du_inl'7580'_376 ::
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_inl'7580'_376 v0
  = coe MAlonzo.Code.Once.Spec.Core.Derived.du_inl'7580'_272
-- Once.Spec.Core.DerivedTyping._.inrᶜ
d_inr'7580'_378 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_inr'7580'_378 ~v0 ~v1 ~v2 = du_inr'7580'_378
du_inr'7580'_378 ::
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_inr'7580'_378 v0
  = coe MAlonzo.Code.Once.Spec.Core.Derived.du_inr'7580'_276
-- Once.Spec.Core.DerivedTyping._.inᶜ
d_in'7580'_380 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_in'7580'_380 ~v0 ~v1 ~v2 = du_in'7580'_380
du_in'7580'_380 ::
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_in'7580'_380 v0
  = coe MAlonzo.Code.Once.Spec.Core.Derived.du_in'7580'_292
-- Once.Spec.Core.DerivedTyping._.outEffᶜ
d_outEff'7580'_384 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_outEff'7580'_384 ~v0 ~v1 ~v2 = du_outEff'7580'_384
du_outEff'7580'_384 ::
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_outEff'7580'_384 v0
  = coe MAlonzo.Code.Once.Spec.Core.Derived.du_outEff'7580'_362
-- Once.Spec.Core.DerivedTyping._.outᶜ
d_out'7580'_386 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_out'7580'_386 ~v0 ~v1 ~v2 = du_out'7580'_386
du_out'7580'_386 ::
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_out'7580'_386 v0
  = coe MAlonzo.Code.Once.Spec.Core.Derived.du_out'7580'_296
-- Once.Spec.Core.DerivedTyping._.pairᶜ
d_pair'7580'_388 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_pair'7580'_388 ~v0 ~v1 ~v2 = du_pair'7580'_388
du_pair'7580'_388 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_pair'7580'_388 v0 v1 v2
  = coe MAlonzo.Code.Once.Spec.Core.Derived.du_pair'7580'_308 v1 v2
-- Once.Spec.Core.DerivedTyping._.sndᶜ
d_snd'7580'_392 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_snd'7580'_392 ~v0 ~v1 ~v2 = du_snd'7580'_392
du_snd'7580'_392 ::
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_snd'7580'_392 v0
  = coe MAlonzo.Code.Once.Spec.Core.Derived.du_snd'7580'_268
-- Once.Spec.Core.DerivedTyping._.terminalᶜ
d_terminal'7580'_394 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_terminal'7580'_394 ~v0 ~v1 ~v2 = du_terminal'7580'_394
du_terminal'7580'_394 ::
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_terminal'7580'_394 v0
  = coe MAlonzo.Code.Once.Spec.Core.Derived.du_terminal'7580'_280
-- Once.Spec.Core.DerivedTyping.⊢var′
d_'8866'var'8242'_404 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'var'8242'_404 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8866'var'8242'_404 v4
du_'8866'var'8242'_404 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'var'8242'_404 v0
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
      (coe MAlonzo.Code.Once.Type.C_pure_34)
      (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v0))
      (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)
-- Once.Spec.Core.DerivedTyping.⊢idᶜ
d_'8866'id'7580'_418 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'id'7580'_418 ~v0 ~v1 ~v2 ~v3 v4 = du_'8866'id'7580'_418 v4
du_'8866'id'7580'_418 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'id'7580'_418 v0
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
         (coe MAlonzo.Code.Once.Type.C_pure_34)
         (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v0))
         (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))
-- Once.Spec.Core.DerivedTyping.⊢fstᶜ
d_'8866'fst'7580'_432 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'fst'7580'_432 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'8866'fst'7580'_432 v4 v5
du_'8866'fst'7580'_432 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'fst'7580'_432 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'fst_358 v0
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
            (coe MAlonzo.Code.Once.Type.C_pure_34)
            (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v1))
            (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)))
-- Once.Spec.Core.DerivedTyping.⊢sndᶜ
d_'8866'snd'7580'_446 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'snd'7580'_446 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8866'snd'7580'_446 v3 v5
du_'8866'snd'7580'_446 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'snd'7580'_446 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'snd_374 v0
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
            (coe MAlonzo.Code.Once.Type.C_pure_34)
            (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v1))
            (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)))
-- Once.Spec.Core.DerivedTyping.⊢inlᶜ
d_'8866'inl'7580'_460 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'inl'7580'_460 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8866'inl'7580'_460 v5
du_'8866'inl'7580'_460 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'inl'7580'_460 v0
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'inl_390
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
            (coe MAlonzo.Code.Once.Type.C_pure_34)
            (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v0))
            (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)))
-- Once.Spec.Core.DerivedTyping.⊢inrᶜ
d_'8866'inr'7580'_474 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'inr'7580'_474 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8866'inr'7580'_474 v5
du_'8866'inr'7580'_474 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'inr'7580'_474 v0
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'inr_406
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
            (coe MAlonzo.Code.Once.Type.C_pure_34)
            (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v0))
            (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)))
-- Once.Spec.Core.DerivedTyping.⊢terminalᶜ
d_'8866'terminal'7580'_486 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'terminal'7580'_486 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8866'terminal'7580'_486 v4
du_'8866'terminal'7580'_486 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'terminal'7580'_486 v0
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
      (coe MAlonzo.Code.Once.Type.C_Zero_6)
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
         (coe MAlonzo.Code.Once.Type.C_pure_34)
         (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v0))
         (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'unit_322))
-- Once.Spec.Core.DerivedTyping.⊢initialᶜ
d_'8866'initial'7580'_498 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'initial'7580'_498 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8866'initial'7580'_498 v4
du_'8866'initial'7580'_498 ::
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'initial'7580'_498 v0
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'absurd_448
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
            (coe MAlonzo.Code.Once.Type.C_pure_34)
            (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v0))
            (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)))
-- Once.Spec.Core.DerivedTyping.z+qz
d_z'43'qz_506 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_z'43'qz_506 = erased
-- Once.Spec.Core.DerivedTyping.z⊔z
d_z'8852'z_514 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_z'8852'z_514 = erased
-- Once.Spec.Core.DerivedTyping.arms
d_arms_530 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Quantity_4 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arms_530 = erased
-- Once.Spec.Core.DerivedTyping.wk-⊢′
d_wk'45''8866''8242'_552 ::
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
d_wk'45''8866''8242'_552 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
  = du_wk'45''8866''8242'_552 v4 v5 v6 v7 v8 v9 v10
du_wk'45''8866''8242'_552 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_wk'45''8866''8242'_552 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Spec.Core.Rename.du_wk'45''8866'_894 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
-- Once.Spec.Core.DerivedTyping.⊢composeᶜ
d_'8866'compose'7580'_584 ::
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
d_'8866'compose'7580'_584 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11
                          v12 v13 v14
  = du_'8866'compose'7580'_584 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v14
du_'8866'compose'7580'_584 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'compose'7580'_584 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'let_316 v2
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
            (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
               (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                  (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))))))
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v3)))
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v5)
         (coe
            MAlonzo.Code.Once.Type.C_mk'45'kind_50
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7))
         (coe v6))
      v9
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'let_316
         (coe
            MAlonzo.Code.Once.Surface.Context.C__'8759'__66
            (coe MAlonzo.Code.Once.Type.C_Zero_6) v3)
         (coe
            MAlonzo.Code.Once.Surface.Context.C__'8759'__66
            (MAlonzo.Code.Once.Type.d__'43'q__12
               (coe MAlonzo.Code.Once.Type.C_One_8)
               (coe
                  MAlonzo.Code.Once.Type.d__'42'q__16
                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe
                     MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)))))
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
               (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                     (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
                     (coe
                        MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0)))))))
         (coe MAlonzo.Code.Once.Type.C_Many_10)
         (coe
            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v4)
            (coe
               MAlonzo.Code.Once.Type.C_mk'45'kind_50
               (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7))
            (coe v5))
         (coe
            du_wk'45''8866''8242'_552 (coe v1) (coe v3) (coe v8)
            (coe
               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v4)
               (coe
                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7))
               (coe v5))
            (coe MAlonzo.Code.Once.Type.C_pure_34)
            (coe
               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v5)
               (coe
                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7))
               (coe v6))
            (coe v10))
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
            (MAlonzo.Code.Once.Type.d__'43'q__12
               (coe MAlonzo.Code.Once.Type.C_Zero_6)
               (coe
                  MAlonzo.Code.Once.Type.d__'42'q__16
                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe
                     MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_One_8)))))
            (coe
               MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'app_294
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0)))))
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_One_8)))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (MAlonzo.Code.Once.Type.d__'43'q__12
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe
                           MAlonzo.Code.Once.Type.d__'42'q__16
                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (MAlonzo.Code.Once.Type.d__'43'q__12
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe
                              MAlonzo.Code.Once.Type.d__'42'q__16
                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                        (coe
                           MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                           (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                              (coe
                                 MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0)))))))
               (coe MAlonzo.Code.Once.Type.C_Many_10) v5
               (coe
                  MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                  (coe MAlonzo.Code.Once.Type.C_pure_34)
                  (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v7))
                  (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))
               (coe
                  MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'app_294
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0)))))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_One_8)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0)))))
                  (coe MAlonzo.Code.Once.Type.C_Many_10) v4
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                     (coe MAlonzo.Code.Once.Type.C_pure_34)
                     (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v7))
                     (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                     (coe MAlonzo.Code.Once.Type.C_pure_34)
                     (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v7))
                     (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))))))
-- Once.Spec.Core.DerivedTyping.⊢pairᶜ
d_'8866'pair'7580'_630 ::
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
d_'8866'pair'7580'_630 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11
                       v12 v13 v14
  = du_'8866'pair'7580'_630 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v14
du_'8866'pair'7580'_630 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'pair'7580'_630 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'let_316 v2
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
               (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))))
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
               (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0)))))
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_One_8) (coe v3)))
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v4)
         (coe
            MAlonzo.Code.Once.Type.C_mk'45'kind_50
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7))
         (coe v5))
      v9
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'let_316
         (coe
            MAlonzo.Code.Once.Surface.Context.C__'8759'__66
            (coe MAlonzo.Code.Once.Type.C_Zero_6) v3)
         (coe
            MAlonzo.Code.Once.Surface.Context.C__'8759'__66
            (MAlonzo.Code.Once.Type.d__'43'q__12
               (coe
                  MAlonzo.Code.Once.Type.d__'43'q__12
                  (coe MAlonzo.Code.Once.Type.C_One_8)
                  (coe
                     MAlonzo.Code.Once.Type.d__'42'q__16
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)))
               (coe
                  MAlonzo.Code.Once.Type.d__'43'q__12
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)
                  (coe
                     MAlonzo.Code.Once.Type.d__'42'q__16
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_Zero_6))))
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                  (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))))
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                  (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))))))
         (coe MAlonzo.Code.Once.Type.C_One_8)
         (coe
            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v4)
            (coe
               MAlonzo.Code.Once.Type.C_mk'45'kind_50
               (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7))
            (coe v6))
         (coe
            du_wk'45''8866''8242'_552 (coe v1) (coe v3) (coe v8)
            (coe
               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v4)
               (coe
                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7))
               (coe v6))
            (coe MAlonzo.Code.Once.Type.C_pure_34)
            (coe
               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v4)
               (coe
                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7))
               (coe v5))
            (coe v10))
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
            (MAlonzo.Code.Once.Type.d__'43'q__12
               (coe
                  MAlonzo.Code.Once.Type.d__'43'q__12
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)
                  (coe
                     MAlonzo.Code.Once.Type.d__'42'q__16
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_One_8)))
               (coe
                  MAlonzo.Code.Once.Type.d__'43'q__12
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)
                  (coe
                     MAlonzo.Code.Once.Type.d__'42'q__16
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_One_8))))
            (coe
               MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'pair_342
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_One_8)))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (MAlonzo.Code.Once.Type.d__'43'q__12
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Type.d__'42'q__16
                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (MAlonzo.Code.Once.Type.d__'43'q__12
                           (coe MAlonzo.Code.Once.Type.C_One_8)
                           (coe
                              MAlonzo.Code.Once.Type.d__'42'q__16
                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                        (coe
                           MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                           (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                              (coe
                                 MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0)))))))
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_One_8)))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_One_8)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (MAlonzo.Code.Once.Type.d__'43'q__12
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe
                              MAlonzo.Code.Once.Type.d__'42'q__16
                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                        (coe
                           MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                           (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                              (coe
                                 MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0)))))))
               (coe
                  MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'app_294
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_One_8)
                           (MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0)))))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_One_8)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0)))))
                  (coe MAlonzo.Code.Once.Type.C_Many_10) v4
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                     (coe MAlonzo.Code.Once.Type.C_pure_34)
                     (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v7))
                     (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                     (coe MAlonzo.Code.Once.Type.C_pure_34)
                     (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v7))
                     (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)))
               (coe
                  MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'app_294
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0)))))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_One_8)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0)))))
                  (coe MAlonzo.Code.Once.Type.C_Many_10) v4
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                     (coe MAlonzo.Code.Once.Type.C_pure_34)
                     (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v7))
                     (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                     (coe MAlonzo.Code.Once.Type.C_pure_34)
                     (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v7))
                     (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))))))
-- Once.Spec.Core.DerivedTyping.⊢caseᶜ
d_'8866'case'7580'_668 ::
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
d_'8866'case'7580'_668 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11
                       v12 v13 v14
  = du_'8866'case'7580'_668 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v14
du_'8866'case'7580'_668 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'case'7580'_668 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'let_316 v2
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
            (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                  (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))))
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                  (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))))))
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_One_8) (coe v3)))
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v4)
         (coe
            MAlonzo.Code.Once.Type.C_mk'45'kind_50
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7))
         (coe v6))
      v9
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'let_316
         (coe
            MAlonzo.Code.Once.Surface.Context.C__'8759'__66
            (coe MAlonzo.Code.Once.Type.C_Zero_6) v3)
         (coe
            MAlonzo.Code.Once.Surface.Context.C__'8759'__66
            (MAlonzo.Code.Once.Type.d__'43'q__12
               (coe MAlonzo.Code.Once.Type.C_Zero_6)
               (coe
                  MAlonzo.Code.Once.Type.d__'8852'q__24
                  (coe
                     MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_One_8)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                  (coe
                     MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)))))
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
               (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
               (coe
                  MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                     (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
                     (coe
                        MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                     (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
                     (coe
                        MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0)))))))
         (coe MAlonzo.Code.Once.Type.C_One_8)
         (coe
            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v5)
            (coe
               MAlonzo.Code.Once.Type.C_mk'45'kind_50
               (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7))
            (coe v6))
         (coe
            du_wk'45''8866''8242'_552 (coe v1) (coe v3) (coe v8)
            (coe
               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v5)
               (coe
                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7))
               (coe v6))
            (coe MAlonzo.Code.Once.Type.C_pure_34)
            (coe
               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v4)
               (coe
                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v7))
               (coe v6))
            (coe v10))
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
            (MAlonzo.Code.Once.Type.d__'43'q__12
               (coe MAlonzo.Code.Once.Type.C_One_8)
               (coe
                  MAlonzo.Code.Once.Type.d__'8852'q__24
                  (coe
                     MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                  (coe
                     MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)))))
            (coe
               MAlonzo.Code.Once.Spec.Core.Typing.du_'8866'case'8852'_664
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (coe MAlonzo.Code.Once.Type.C_One_8)
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0)))))
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (MAlonzo.Code.Once.Type.d__'43'q__12
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Type.d__'42'q__16
                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (MAlonzo.Code.Once.Type.d__'43'q__12
                           (coe MAlonzo.Code.Once.Type.C_One_8)
                           (coe
                              MAlonzo.Code.Once.Type.d__'42'q__16
                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                        (coe
                           MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                           (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                              (coe
                                 MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0)))))))
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (MAlonzo.Code.Once.Type.d__'43'q__12
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Type.d__'42'q__16
                        (coe MAlonzo.Code.Once.Type.C_Many_10)
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_One_8)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (MAlonzo.Code.Once.Type.d__'43'q__12
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe
                              MAlonzo.Code.Once.Type.d__'42'q__16
                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)))
                        (coe
                           MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                           (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                              (coe
                                 MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0)))))))
               (coe
                  MAlonzo.Code.Once.Type.d__'43'q__12
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)
                  (coe
                     MAlonzo.Code.Once.Type.d__'42'q__16
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_One_8)))
               (coe
                  MAlonzo.Code.Once.Type.d__'43'q__12
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)
                  (coe
                     MAlonzo.Code.Once.Type.d__'42'q__16
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_One_8)))
               (coe v4) (coe v5)
               (coe
                  MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                  (coe MAlonzo.Code.Once.Type.C_pure_34)
                  (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v7))
                  (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))
               (coe
                  MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'app_294
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                              (coe MAlonzo.Code.Once.Type.C_One_8)
                              (MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))))))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_One_8)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)
                              (MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))))))
                  (coe MAlonzo.Code.Once.Type.C_Many_10) v4
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                     (coe MAlonzo.Code.Once.Type.C_pure_34)
                     (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v7))
                     (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                     (coe MAlonzo.Code.Once.Type.C_pure_34)
                     (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v7))
                     (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)))
               (coe
                  MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'app_294
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_One_8)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)
                              (MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))))))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_One_8)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)
                              (MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))))))
                  (coe MAlonzo.Code.Once.Type.C_Many_10) v5
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                     (coe MAlonzo.Code.Once.Type.C_pure_34)
                     (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v7))
                     (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                     (coe MAlonzo.Code.Once.Type.C_pure_34)
                     (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v7))
                     (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))))))
-- Once.Spec.Core.DerivedTyping.⊢curryᶜ
d_'8866'curry'7580'_706 ::
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
d_'8866'curry'7580'_706 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 v8 v9 v10 ~v11
                        v12
  = du_'8866'curry'7580'_706 v3 v5 v6 v7 v8 v9 v10 v12
du_'8866'curry'7580'_706 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'curry'7580'_706 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'let_316 v1
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
         (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_Many_10)
            (coe
               MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
               (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
               (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0)))))
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
         (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v2) (coe v3))
         (coe
            MAlonzo.Code.Once.Type.C_mk'45'kind_50
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v6))
         (coe v4))
      v7
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
         (MAlonzo.Code.Once.Type.d__'43'q__12
            (coe MAlonzo.Code.Once.Type.C_Zero_6)
            (coe
               MAlonzo.Code.Once.Type.d__'42'q__16
               (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe
                  MAlonzo.Code.Once.Type.d__'43'q__12
                  (coe MAlonzo.Code.Once.Type.C_One_8)
                  (coe MAlonzo.Code.Once.Type.C_Zero_6))))
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
            (coe MAlonzo.Code.Once.Type.C_pure_34)
            (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v5))
            (coe
               MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
               (MAlonzo.Code.Once.Type.d__'43'q__12
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)
                  (coe
                     MAlonzo.Code.Once.Type.d__'42'q__16
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe
                        MAlonzo.Code.Once.Type.d__'43'q__12
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe MAlonzo.Code.Once.Type.C_One_8))))
               (coe
                  MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'app_294
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (coe MAlonzo.Code.Once.Type.C_Zero_6)
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_One_8)
                           (MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0)))))
                  (coe
                     MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                     (MAlonzo.Code.Once.Type.d__'43'q__12
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe MAlonzo.Code.Once.Type.C_One_8))
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (MAlonzo.Code.Once.Type.d__'43'q__12
                           (coe MAlonzo.Code.Once.Type.C_One_8)
                           (coe MAlonzo.Code.Once.Type.C_Zero_6))
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (MAlonzo.Code.Once.Type.d__'43'q__12
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)
                              (coe MAlonzo.Code.Once.Type.C_Zero_6))
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                              (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
                              (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))))))
                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v2) (coe v3))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                     (coe MAlonzo.Code.Once.Type.C_pure_34)
                     (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v6))
                     (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'pair_342
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_Zero_6)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_One_8)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)
                              (MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0)))))
                     (coe
                        MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                        (coe MAlonzo.Code.Once.Type.C_One_8)
                        (coe
                           MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                           (coe MAlonzo.Code.Once.Type.C_Zero_6)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                              (coe MAlonzo.Code.Once.Type.C_Zero_6)
                              (MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0)))))
                     (coe
                        MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                        (coe MAlonzo.Code.Once.Type.C_pure_34)
                        (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v6))
                        (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))
                     (coe
                        MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                        (coe MAlonzo.Code.Once.Type.C_pure_34)
                        (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v6))
                        (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)))))))
-- Once.Spec.Core.DerivedTyping.⊢cataᶜ
d_'8866'cata'7580'_738 ::
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
d_'8866'cata'7580'_738 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 v8 ~v9 v10 v11
  = du_'8866'cata'7580'_738 v3 v5 v6 v7 v8 v10 v11
du_'8866'cata'7580'_738 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'cata'7580'_738 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'let_316 v1
      (coe
         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
         (coe
            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
            (coe MAlonzo.Code.Once.Type.C_Many_10)
            (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0)))
         (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0)))
      (coe MAlonzo.Code.Once.Type.C_Many_10)
      (coe
         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
         (coe
            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v2) (coe v3))
         (coe
            MAlonzo.Code.Once.Type.C_mk'45'kind_50
            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v4))
         (coe v3))
      v6
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
         (MAlonzo.Code.Once.Type.d__'43'q__12
            (coe
               MAlonzo.Code.Once.Type.d__'42'q__16
               (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe MAlonzo.Code.Once.Type.C_Zero_6))
            (coe MAlonzo.Code.Once.Type.C_One_8))
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'fold_482
            (coe
               MAlonzo.Code.Once.Surface.Context.C__'8759'__66
               (coe MAlonzo.Code.Once.Type.C_Zero_6)
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (coe MAlonzo.Code.Once.Type.C_One_8)
                  (MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))))
            (coe
               MAlonzo.Code.Once.Surface.Context.C__'8759'__66
               (coe MAlonzo.Code.Once.Type.C_One_8)
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (coe MAlonzo.Code.Once.Type.C_Zero_6)
                  (MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))))
            v2 v5
            (coe
               MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
               (coe MAlonzo.Code.Once.Type.C_pure_34)
               (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v4))
               (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))
            (coe
               MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
               (coe MAlonzo.Code.Once.Type.C_pure_34)
               (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v4))
               (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))))
-- Once.Spec.Core.DerivedTyping.⊢anaᶜ
d_'8866'ana'7580'_772 ::
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
d_'8866'ana'7580'_772 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = du_'8866'ana'7580'_772 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
du_'8866'ana'7580'_772 ::
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
du_'8866'ana'7580'_772 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'unfold_504
         (coe
            MAlonzo.Code.Once.Surface.Context.C__'8759'__66
            (coe MAlonzo.Code.Once.Type.C_Zero_6) v2)
         (coe
            MAlonzo.Code.Once.Surface.Context.C__'8759'__66
            (coe MAlonzo.Code.Once.Type.C_One_8)
            (MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0)))
         v4 v8
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
            (coe MAlonzo.Code.Once.Type.C_pure_34)
            (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v5))
            (coe
               du_wk'45''8866''8242'_552 (coe v1) (coe v2) (coe v7)
               (coe
                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v4)
                  (coe
                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                     (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v6))
                  (coe
                     MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v3) (coe v4)))
               (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v4) (coe v9)))
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
            (coe MAlonzo.Code.Once.Type.C_pure_34)
            (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16 (coe v5))
            (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)))
-- Once.Spec.Core.DerivedTyping.⊢applyᶜ
d_'8866'apply'7580'_796 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'apply'7580'_796 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_'8866'apply'7580'_796 v3 v5 v6
du_'8866'apply'7580'_796 ::
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'apply'7580'_796 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
      (MAlonzo.Code.Once.Type.d__'43'q__12
         (coe MAlonzo.Code.Once.Type.C_One_8)
         (coe
            MAlonzo.Code.Once.Type.d__'42'q__16
            (coe MAlonzo.Code.Once.Type.C_Many_10)
            (coe MAlonzo.Code.Once.Type.C_One_8)))
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'app_294
         (coe
            MAlonzo.Code.Once.Surface.Context.C__'8759'__66
            (coe MAlonzo.Code.Once.Type.C_One_8)
            (MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0)))
         (coe
            MAlonzo.Code.Once.Surface.Context.C__'8759'__66
            (coe MAlonzo.Code.Once.Type.C_One_8)
            (MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0)))
         (coe MAlonzo.Code.Once.Type.C_Many_10) v1
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'fst_358 v1
            (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'snd_374
            (coe
               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v1)
               (coe
                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                  (coe MAlonzo.Code.Once.Type.C_pure_34))
               (coe v2))
            (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)))
-- Once.Spec.Core.DerivedTyping.⊢inᶜ
d_'8866'in'7580'_808 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'in'7580'_808 ~v0 ~v1 ~v2 ~v3 v4 = du_'8866'in'7580'_808 v4
du_'8866'in'7580'_808 ::
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'in'7580'_808 v0
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'roll_462 v0
         (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))
-- Once.Spec.Core.DerivedTyping.⊢outᶜ
d_'8866'out'7580'_818 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'out'7580'_818 ~v0 ~v1 ~v2 v3 v4
  = du_'8866'out'7580'_818 v3 v4
du_'8866'out'7580'_818 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'out'7580'_818 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'out_518 v0 v1
         (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))
-- Once.Spec.Core.DerivedTyping.⊢applyEffᶜ
d_'8866'applyEff'7580'_830 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'applyEff'7580'_830 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_'8866'applyEff'7580'_830 v3 v5 v6
du_'8866'applyEff'7580'_830 ::
  Integer ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'applyEff'7580'_830 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
      (MAlonzo.Code.Once.Type.d__'43'q__12
         (coe MAlonzo.Code.Once.Type.C_One_8)
         (coe
            MAlonzo.Code.Once.Type.d__'42'q__16
            (coe MAlonzo.Code.Once.Type.C_Many_10)
            (coe MAlonzo.Code.Once.Type.C_One_8)))
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
         (MAlonzo.Code.Once.Type.d__'43'q__12
            (coe MAlonzo.Code.Once.Type.C_Zero_6)
            (coe
               MAlonzo.Code.Once.Type.d__'42'q__16
               (coe MAlonzo.Code.Once.Type.C_Many_10)
               (coe MAlonzo.Code.Once.Type.C_Zero_6)))
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'app_294
            (coe
               MAlonzo.Code.Once.Surface.Context.C__'8759'__66
               (coe MAlonzo.Code.Once.Type.C_Zero_6)
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (coe MAlonzo.Code.Once.Type.C_One_8)
                  (MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))))
            (coe
               MAlonzo.Code.Once.Surface.Context.C__'8759'__66
               (coe MAlonzo.Code.Once.Type.C_Zero_6)
               (coe
                  MAlonzo.Code.Once.Surface.Context.C__'8759'__66
                  (coe MAlonzo.Code.Once.Type.C_One_8)
                  (MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))))
            (coe MAlonzo.Code.Once.Type.C_Many_10) v1
            (coe
               MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'fst_358 v1
               (coe
                  MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                  (coe MAlonzo.Code.Once.Type.C_pure_34)
                  (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16
                     (coe MAlonzo.Code.Once.Type.C_eff_36))
                  (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)))
            (coe
               MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'snd_374
               (coe
                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v1)
                  (coe
                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_eff_36))
                  (coe v2))
               (coe
                  MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                  (coe MAlonzo.Code.Once.Type.C_pure_34)
                  (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16
                     (coe MAlonzo.Code.Once.Type.C_eff_36))
                  (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)))))
-- Once.Spec.Core.DerivedTyping.⊢outEffᶜ
d_'8866'outEff'7580'_842 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'outEff'7580'_842 ~v0 ~v1 ~v2 v3 v4
  = du_'8866'outEff'7580'_842 v3 v4
du_'8866'outEff'7580'_842 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'outEff'7580'_842 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
      (coe MAlonzo.Code.Once.Type.C_One_8)
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
         (coe MAlonzo.Code.Once.Type.C_Zero_6)
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'out_518 v0 v1
            (coe
               MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
               (coe MAlonzo.Code.Once.Type.C_pure_34)
               (MAlonzo.Code.Once.Type.Sub.d_pure'8849'_16
                  (coe MAlonzo.Code.Once.Type.C_eff_36))
               (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))))
-- Once.Spec.Core.DerivedTyping.⊢effAppᶜ
d_'8866'effApp'7580'_862 ::
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
d_'8866'effApp'7580'_862 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11
                         v12
  = du_'8866'effApp'7580'_862 v4 v5 v6 v7 v8 v9 v10 v11 v12
du_'8866'effApp'7580'_862 ::
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
du_'8866'effApp'7580'_862 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
      (MAlonzo.Code.Once.Type.d__'43'q__12
         (coe MAlonzo.Code.Once.Type.C_Zero_6)
         (coe
            MAlonzo.Code.Once.Type.d__'42'q__16
            (coe MAlonzo.Code.Once.Type.C_Many_10)
            (coe MAlonzo.Code.Once.Type.C_Zero_6)))
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'app_294
         (coe
            MAlonzo.Code.Once.Surface.Context.C__'8759'__66
            (coe MAlonzo.Code.Once.Type.C_Zero_6) v1)
         (coe
            MAlonzo.Code.Once.Surface.Context.C__'8759'__66
            (coe MAlonzo.Code.Once.Type.C_Zero_6) v2)
         (coe MAlonzo.Code.Once.Type.C_Many_10) v3
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
            (coe MAlonzo.Code.Once.Type.C_pure_34)
            (coe MAlonzo.Code.Once.Type.Sub.C_'8849''45'pe_12)
            (coe
               du_wk'45''8866''8242'_552 (coe v0) (coe v1) (coe v5)
               (coe
                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v3)
                  (coe
                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                     (coe MAlonzo.Code.Once.Type.C_eff_36))
                  (coe v4))
               (coe MAlonzo.Code.Once.Type.C_pure_34)
               (coe MAlonzo.Code.Once.Type.C_Unit_120) (coe v7)))
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
            (coe MAlonzo.Code.Once.Type.C_pure_34)
            (coe MAlonzo.Code.Once.Type.Sub.C_'8849''45'pe_12)
            (coe
               du_wk'45''8866''8242'_552 (coe v0) (coe v2) (coe v6) (coe v3)
               (coe MAlonzo.Code.Once.Type.C_pure_34)
               (coe MAlonzo.Code.Once.Type.C_Unit_120) (coe v8))))
-- Once.Spec.Core.DerivedTyping.⊢seqᶜ
d_'8866'seq'7580'_886 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_864 ->
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'seq'7580'_886 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 ~v7 ~v8 ~v9 v10 v11
  = du_'8866'seq'7580'_886 v3 v4 v5 v10 v11
du_'8866'seq'7580'_886 ::
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'seq'7580'_886 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'snd_374 v2
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'pair_342 v0 v1 v3 v4)
