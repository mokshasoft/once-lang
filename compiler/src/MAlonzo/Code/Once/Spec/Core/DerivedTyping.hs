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
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Core.Derived
import qualified MAlonzo.Code.Once.Spec.Core.PolyTy
import qualified MAlonzo.Code.Once.Spec.Core.Rename
import qualified MAlonzo.Code.Once.Spec.Core.Syntax
import qualified MAlonzo.Code.Once.Spec.Core.Typing
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Spec.Type.Grade
import qualified MAlonzo.Code.Once.Spec.Type.Sub
import qualified MAlonzo.Code.Once.Spec.Type.WellFormed

-- Once.Spec.Core.DerivedTyping._.Tm
d_Tm_30 a0 a1 a2 a3 = ()
-- Once.Spec.Core.DerivedTyping._.wk
d_wk_142 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
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
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
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
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_applyEff'7580'_356 ~v0 ~v1 ~v2 = du_applyEff'7580'_356
du_applyEff'7580'_356 ::
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_applyEff'7580'_356 v0
  = coe MAlonzo.Code.Once.Spec.Core.Derived.du_applyEff'7580'_350
-- Once.Spec.Core.DerivedTyping._.applyᶜ
d_apply'7580'_358 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
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
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
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
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
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
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
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
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
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
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
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
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
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
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
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
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
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
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
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
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_in'7580'_380 ~v0 ~v1 ~v2 = du_in'7580'_380
du_in'7580'_380 ::
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_in'7580'_380 v0
  = coe MAlonzo.Code.Once.Spec.Core.Derived.du_in'7580'_292
-- Once.Spec.Core.DerivedTyping._.outEffᶜ
d_outEff'7580'_382 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_outEff'7580'_382 ~v0 ~v1 ~v2 = du_outEff'7580'_382
du_outEff'7580'_382 ::
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_outEff'7580'_382 v0
  = coe MAlonzo.Code.Once.Spec.Core.Derived.du_outEff'7580'_354
-- Once.Spec.Core.DerivedTyping._.outᶜ
d_out'7580'_384 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_out'7580'_384 ~v0 ~v1 ~v2 = du_out'7580'_384
du_out'7580'_384 ::
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_out'7580'_384 v0
  = coe MAlonzo.Code.Once.Spec.Core.Derived.du_out'7580'_296
-- Once.Spec.Core.DerivedTyping._.pairᶜ
d_pair'7580'_386 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_pair'7580'_386 ~v0 ~v1 ~v2 = du_pair'7580'_386
du_pair'7580'_386 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_pair'7580'_386 v0 v1 v2
  = coe MAlonzo.Code.Once.Spec.Core.Derived.du_pair'7580'_308 v1 v2
-- Once.Spec.Core.DerivedTyping._.sndᶜ
d_snd'7580'_388 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_snd'7580'_388 ~v0 ~v1 ~v2 = du_snd'7580'_388
du_snd'7580'_388 ::
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_snd'7580'_388 v0
  = coe MAlonzo.Code.Once.Spec.Core.Derived.du_snd'7580'_268
-- Once.Spec.Core.DerivedTyping._.terminalᶜ
d_terminal'7580'_390 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
d_terminal'7580'_390 ~v0 ~v1 ~v2 = du_terminal'7580'_390
du_terminal'7580'_390 ::
  Integer -> MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62
du_terminal'7580'_390 v0
  = coe MAlonzo.Code.Once.Spec.Core.Derived.du_terminal'7580'_280
-- Once.Spec.Core.DerivedTyping.⊢var′
d_'8866'var'8242'_400 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'var'8242'_400 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8866'var'8242'_400 v4
du_'8866'var'8242'_400 ::
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'var'8242'_400 v0
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
      (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
      (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18 (coe v0))
      (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)
-- Once.Spec.Core.DerivedTyping.⊢idᶜ
d_'8866'id'7580'_414 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'id'7580'_414 ~v0 ~v1 ~v2 ~v3 v4 = du_'8866'id'7580'_414 v4
du_'8866'id'7580'_414 ::
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'id'7580'_414 v0
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
      (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
         (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
         (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18 (coe v0))
         (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))
-- Once.Spec.Core.DerivedTyping.⊢fstᶜ
d_'8866'fst'7580'_428 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'fst'7580'_428 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'8866'fst'7580'_428 v4 v5
du_'8866'fst'7580'_428 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'fst'7580'_428 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
      (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'fst_358 v0
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
            (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18 (coe v1))
            (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)))
-- Once.Spec.Core.DerivedTyping.⊢sndᶜ
d_'8866'snd'7580'_442 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'snd'7580'_442 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8866'snd'7580'_442 v3 v5
du_'8866'snd'7580'_442 ::
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'snd'7580'_442 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
      (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'snd_374 v0
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
            (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18 (coe v1))
            (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)))
-- Once.Spec.Core.DerivedTyping.⊢inlᶜ
d_'8866'inl'7580'_456 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'inl'7580'_456 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8866'inl'7580'_456 v5
du_'8866'inl'7580'_456 ::
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'inl'7580'_456 v0
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
      (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'inl_390
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
            (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18 (coe v0))
            (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)))
-- Once.Spec.Core.DerivedTyping.⊢inrᶜ
d_'8866'inr'7580'_470 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'inr'7580'_470 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8866'inr'7580'_470 v5
du_'8866'inr'7580'_470 ::
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'inr'7580'_470 v0
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
      (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'inr_406
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
            (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18 (coe v0))
            (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)))
-- Once.Spec.Core.DerivedTyping.⊢terminalᶜ
d_'8866'terminal'7580'_482 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'terminal'7580'_482 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8866'terminal'7580'_482 v4
du_'8866'terminal'7580'_482 ::
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'terminal'7580'_482 v0
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
      (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
         (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
         (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18 (coe v0))
         (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'unit_322))
-- Once.Spec.Core.DerivedTyping.⊢initialᶜ
d_'8866'initial'7580'_494 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'initial'7580'_494 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8866'initial'7580'_494 v4
du_'8866'initial'7580'_494 ::
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'initial'7580'_494 v0
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
      (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'absurd_448
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
            (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18 (coe v0))
            (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)))
-- Once.Spec.Core.DerivedTyping.z+qz
d_z'43'qz_502 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_z'43'qz_502 = erased
-- Once.Spec.Core.DerivedTyping.z⊔z
d_z'8852'z_510 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_z'8852'z_510 = erased
-- Once.Spec.Core.DerivedTyping.arms
d_arms_526 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arms_526 = erased
-- Once.Spec.Core.DerivedTyping.wk-⊢′
d_wk'45''8866''8242'_548 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_wk'45''8866''8242'_548 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
  = du_wk'45''8866''8242'_548 v4 v5 v6 v7 v8 v9 v10
du_wk'45''8866''8242'_548 ::
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_wk'45''8866''8242'_548 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Spec.Core.Rename.du_wk'45''8866'_894 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6)
-- Once.Spec.Core.DerivedTyping.⊢composeᶜ
d_'8866'compose'7580'_580 ::
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
d_'8866'compose'7580'_580 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11
                          v12 v13 v14
  = du_'8866'compose'7580'_580 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v14
du_'8866'compose'7580'_580 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'compose'7580'_580 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'let_316 v2
      (coe
         MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76
         (coe
            MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76
            (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))
            (coe
               MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
               (coe
                  MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76
                  (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))
                  (coe
                     MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                     (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))))))
         (coe
            MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) (coe v3)))
      (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 (coe v5)
         (coe
            MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) (coe v7))
         (coe v6))
      v9
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'let_316
         (coe
            MAlonzo.Code.Once.Spec.Context.C__'8759'__52
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10) v3)
         (coe
            MAlonzo.Code.Once.Spec.Context.C__'8759'__52
            (MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
               (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
               (coe
                  MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                  (coe
                     MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                     (coe
                        MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)))))
            (coe
               MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76
               (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))
               (coe
                  MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                  (coe
                     MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76
                     (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))
                     (coe
                        MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                        (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0)))))))
         (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
         (coe
            MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 (coe v4)
            (coe
               MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48
               (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) (coe v7))
            (coe v5))
         (coe
            du_wk'45''8866''8242'_548 (coe v1) (coe v3) (coe v8)
            (coe
               MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 (coe v4)
               (coe
                  MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) (coe v7))
               (coe v5))
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
            (coe
               MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 (coe v5)
               (coe
                  MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) (coe v7))
               (coe v6))
            (coe v10))
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
            (MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
               (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
               (coe
                  MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                  (coe
                     MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                     (coe
                        MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)))))
            (coe
               MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'app_294
               (coe
                  MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
                        (MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0)))))
               (coe
                  MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                  (MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                     (coe
                        MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)))
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                     (MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
                        (coe
                           MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
                           (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                           (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)))
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                        (MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
                           (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                           (coe
                              MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
                              (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                              (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)))
                        (coe
                           MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76
                           (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))
                           (coe
                              MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
                              (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                              (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0)))))))
               (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) v5
               (coe
                  MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
                  (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18 (coe v7))
                  (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))
               (coe
                  MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'app_294
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
                        (coe
                           MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                           (MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0)))))
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                        (coe
                           MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                           (MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0)))))
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) v4
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
                     (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18 (coe v7))
                     (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
                     (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18 (coe v7))
                     (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))))))
-- Once.Spec.Core.DerivedTyping.⊢pairᶜ
d_'8866'pair'7580'_626 ::
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
d_'8866'pair'7580'_626 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11
                       v12 v13 v14
  = du_'8866'pair'7580'_626 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v14
du_'8866'pair'7580'_626 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'pair'7580'_626 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'let_316 v2
      (coe
         MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76
         (coe
            MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76
            (coe
               MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76
               (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))
               (coe
                  MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                  (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))))
            (coe
               MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76
               (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))
               (coe
                  MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                  (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0)))))
         (coe
            MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12) (coe v3)))
      (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 (coe v4)
         (coe
            MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) (coe v7))
         (coe v5))
      v9
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'let_316
         (coe
            MAlonzo.Code.Once.Spec.Context.C__'8759'__52
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10) v3)
         (coe
            MAlonzo.Code.Once.Spec.Context.C__'8759'__52
            (MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
               (coe
                  MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
                  (coe
                     MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)))
               (coe
                  MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                  (coe
                     MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10))))
            (coe
               MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76
               (coe
                  MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76
                  (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))
                  (coe
                     MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                     (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))))
               (coe
                  MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76
                  (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))
                  (coe
                     MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                     (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))))))
         (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
         (coe
            MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 (coe v4)
            (coe
               MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48
               (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) (coe v7))
            (coe v6))
         (coe
            du_wk'45''8866''8242'_548 (coe v1) (coe v3) (coe v8)
            (coe
               MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 (coe v4)
               (coe
                  MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) (coe v7))
               (coe v6))
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
            (coe
               MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 (coe v4)
               (coe
                  MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) (coe v7))
               (coe v5))
            (coe v10))
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
            (MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
               (coe
                  MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                  (coe
                     MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)))
               (coe
                  MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                  (coe
                     MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12))))
            (coe
               MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'pair_342
               (coe
                  MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                  (MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                     (coe
                        MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)))
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                     (MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                        (coe
                           MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
                           (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                           (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)))
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                        (MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
                           (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
                           (coe
                              MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
                              (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                              (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)))
                        (coe
                           MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76
                           (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))
                           (coe
                              MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
                              (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                              (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0)))))))
               (coe
                  MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                  (MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                     (coe
                        MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)))
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                        (MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
                           (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                           (coe
                              MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
                              (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                              (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)))
                        (coe
                           MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76
                           (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))
                           (coe
                              MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
                              (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                              (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0)))))))
               (coe
                  MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'app_294
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                        (coe
                           MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
                           (MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0)))))
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                        (coe
                           MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                           (MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0)))))
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) v4
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
                     (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18 (coe v7))
                     (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
                     (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18 (coe v7))
                     (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)))
               (coe
                  MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'app_294
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
                        (coe
                           MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                           (MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0)))))
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                        (coe
                           MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                           (MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0)))))
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) v4
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
                     (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18 (coe v7))
                     (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
                     (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18 (coe v7))
                     (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))))))
-- Once.Spec.Core.DerivedTyping.⊢caseᶜ
d_'8866'case'7580'_664 ::
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
d_'8866'case'7580'_664 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11
                       v12 v13 v14
  = du_'8866'case'7580'_664 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v14
du_'8866'case'7580'_664 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'case'7580'_664 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'let_316 v2
      (coe
         MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76
         (coe
            MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76
            (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))
            (coe
               MAlonzo.Code.Once.Spec.Context.du__'8852''7512'__100
               (coe
                  MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76
                  (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))
                  (coe
                     MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                     (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))))
               (coe
                  MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76
                  (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))
                  (coe
                     MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                     (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))))))
         (coe
            MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12) (coe v3)))
      (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 (coe v4)
         (coe
            MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) (coe v7))
         (coe v6))
      v9
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'let_316
         (coe
            MAlonzo.Code.Once.Spec.Context.C__'8759'__52
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10) v3)
         (coe
            MAlonzo.Code.Once.Spec.Context.C__'8759'__52
            (MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
               (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
               (coe
                  MAlonzo.Code.Once.Spec.Type.Grade.d__'8852'q__22
                  (coe
                     MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
                     (coe
                        MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)))
                  (coe
                     MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                     (coe
                        MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)))))
            (coe
               MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76
               (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))
               (coe
                  MAlonzo.Code.Once.Spec.Context.du__'8852''7512'__100
                  (coe
                     MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76
                     (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))
                     (coe
                        MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                        (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))))
                  (coe
                     MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76
                     (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))
                     (coe
                        MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                        (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0)))))))
         (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
         (coe
            MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 (coe v5)
            (coe
               MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48
               (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) (coe v7))
            (coe v6))
         (coe
            du_wk'45''8866''8242'_548 (coe v1) (coe v3) (coe v8)
            (coe
               MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 (coe v5)
               (coe
                  MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) (coe v7))
               (coe v6))
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
            (coe
               MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 (coe v4)
               (coe
                  MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) (coe v7))
               (coe v6))
            (coe v10))
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
            (MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
               (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
               (coe
                  MAlonzo.Code.Once.Spec.Type.Grade.d__'8852'q__22
                  (coe
                     MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                     (coe
                        MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)))
                  (coe
                     MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                     (coe
                        MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)))))
            (coe
               MAlonzo.Code.Once.Spec.Core.Typing.du_'8866'case'8852'_664
               (coe
                  MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                        (MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0)))))
               (coe
                  MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                  (MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                     (coe
                        MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)))
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                     (MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                        (coe
                           MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
                           (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                           (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)))
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                        (MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
                           (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
                           (coe
                              MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
                              (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                              (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)))
                        (coe
                           MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76
                           (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))
                           (coe
                              MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
                              (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                              (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0)))))))
               (coe
                  MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                  (MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                     (coe
                        MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)))
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                        (MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
                           (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                           (coe
                              MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
                              (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                              (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)))
                        (coe
                           MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76
                           (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))
                           (coe
                              MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
                              (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                              (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0)))))))
               (coe
                  MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                  (coe
                     MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)))
               (coe
                  MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                  (coe
                     MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)))
               (coe v4) (coe v5)
               (coe
                  MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
                  (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18 (coe v7))
                  (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))
               (coe
                  MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'app_294
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                        (coe
                           MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                           (coe
                              MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                              (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
                              (MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))))))
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                        (coe
                           MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                           (coe
                              MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                              (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                              (MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))))))
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) v4
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
                     (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18 (coe v7))
                     (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
                     (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18 (coe v7))
                     (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)))
               (coe
                  MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'app_294
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                        (coe
                           MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
                           (coe
                              MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                              (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                              (MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))))))
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                        (coe
                           MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                           (coe
                              MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                              (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                              (MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))))))
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) v5
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
                     (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18 (coe v7))
                     (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
                     (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18 (coe v7))
                     (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))))))
-- Once.Spec.Core.DerivedTyping.⊢curryᶜ
d_'8866'curry'7580'_702 ::
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
d_'8866'curry'7580'_702 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 v8 v9 v10 ~v11
                        v12
  = du_'8866'curry'7580'_702 v3 v5 v6 v7 v8 v9 v10 v12
du_'8866'curry'7580'_702 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'curry'7580'_702 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'let_316 v1
      (coe
         MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76
         (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))
         (coe
            MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
            (coe
               MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76
               (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))
               (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0)))))
      (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28
         (coe MAlonzo.Code.Once.Spec.Type.C__'42'__24 (coe v2) (coe v3))
         (coe
            MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) (coe v6))
         (coe v4))
      v7
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
         (MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
            (coe
               MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
               (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
               (coe
                  MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10))))
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
            (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18 (coe v5))
            (coe
               MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
               (MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                  (coe
                     MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                     (coe
                        MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12))))
               (coe
                  MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'app_294
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                        (coe
                           MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
                           (MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0)))))
                  (coe
                     MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                     (MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12))
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                        (MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
                           (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
                           (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10))
                        (coe
                           MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                           (MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
                              (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                              (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10))
                           (coe
                              MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76
                              (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))
                              (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))))))
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                  (coe MAlonzo.Code.Once.Spec.Type.C__'42'__24 (coe v2) (coe v3))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
                     (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18 (coe v6))
                     (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))
                  (coe
                     MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'pair_342
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                        (coe
                           MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
                           (coe
                              MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                              (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                              (MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0)))))
                     (coe
                        MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
                        (coe
                           MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                           (coe
                              MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                              (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                              (MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0)))))
                     (coe
                        MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
                        (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18 (coe v6))
                        (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))
                     (coe
                        MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                        (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
                        (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18 (coe v6))
                        (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)))))))
-- Once.Spec.Core.DerivedTyping.⊢cataᶜ
d_'8866'cata'7580'_734 ::
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
d_'8866'cata'7580'_734 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 v8 ~v9 v10 v11
  = du_'8866'cata'7580'_734 v3 v5 v6 v7 v8 v10 v11
du_'8866'cata'7580'_734 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.Grade.T_Purity_28 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'cata'7580'_734 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'let_316 v1
      (coe
         MAlonzo.Code.Once.Spec.Context.du__'43''7512'__76
         (coe
            MAlonzo.Code.Once.Spec.Context.du__'42''7512'__88
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
            (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0)))
         (coe MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0)))
      (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
      (coe
         MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28
         (coe
            MAlonzo.Code.Once.Spec.Type.d_'10214'_'10215'T_62 (coe v2)
            (coe v3))
         (coe
            MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) (coe v4))
         (coe v3))
      v6
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
         (MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
            (coe
               MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
               (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
               (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10))
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12))
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'fold_482
            (coe
               MAlonzo.Code.Once.Spec.Context.C__'8759'__52
               (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
               (coe
                  MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
                  (MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))))
            (coe
               MAlonzo.Code.Once.Spec.Context.C__'8759'__52
               (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
               (coe
                  MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
                  (MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))))
            v2 v5
            (coe
               MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
               (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
               (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18 (coe v4))
               (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))
            (coe
               MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
               (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
               (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18 (coe v4))
               (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))))
-- Once.Spec.Core.DerivedTyping.⊢anaᶜ
d_'8866'ana'7580'_768 ::
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
d_'8866'ana'7580'_768 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = du_'8866'ana'7580'_768 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
du_'8866'ana'7580'_768 ::
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
du_'8866'ana'7580'_768 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
      (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'unfold_504
         (coe
            MAlonzo.Code.Once.Spec.Context.C__'8759'__52
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10) v2)
         (coe
            MAlonzo.Code.Once.Spec.Context.C__'8759'__52
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
            (MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0)))
         v4 v8
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
            (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18 (coe v5))
            (coe
               du_wk'45''8866''8242'_548 (coe v1) (coe v2) (coe v7)
               (coe
                  MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 (coe v4)
                  (coe
                     MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) (coe v6))
                  (coe
                     MAlonzo.Code.Once.Spec.Type.d_'10214'_'10215'T_62 (coe v3)
                     (coe v4)))
               (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30) (coe v4)
               (coe v9)))
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
            (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18 (coe v5))
            (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)))
-- Once.Spec.Core.DerivedTyping.⊢applyᶜ
d_'8866'apply'7580'_792 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'apply'7580'_792 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_'8866'apply'7580'_792 v3 v5 v6
du_'8866'apply'7580'_792 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'apply'7580'_792 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
      (MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
         (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
         (coe
            MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)))
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'app_294
         (coe
            MAlonzo.Code.Once.Spec.Context.C__'8759'__52
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
            (MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0)))
         (coe
            MAlonzo.Code.Once.Spec.Context.C__'8759'__52
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
            (MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0)))
         (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) v1
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'fst_358 v1
            (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'snd_374
            (coe
               MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 (coe v1)
               (coe
                  MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30))
               (coe v2))
            (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)))
-- Once.Spec.Core.DerivedTyping.⊢inᶜ
d_'8866'in'7580'_804 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'in'7580'_804 ~v0 ~v1 ~v2 ~v3 v4 = du_'8866'in'7580'_804 v4
du_'8866'in'7580'_804 ::
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'in'7580'_804 v0
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
      (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'roll_462 v0
         (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))
-- Once.Spec.Core.DerivedTyping.⊢outᶜ
d_'8866'out'7580'_814 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'out'7580'_814 ~v0 ~v1 ~v2 v3 v4
  = du_'8866'out'7580'_814 v3 v4
du_'8866'out'7580'_814 ::
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'out'7580'_814 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
      (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'out_518 v0 v1
         (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252))
-- Once.Spec.Core.DerivedTyping.⊢applyEffᶜ
d_'8866'applyEff'7580'_826 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'applyEff'7580'_826 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_'8866'applyEff'7580'_826 v3 v5 v6
du_'8866'applyEff'7580'_826 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'applyEff'7580'_826 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
      (MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
         (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
         (coe
            MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)))
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
         (MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
            (coe
               MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
               (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
               (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)))
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'app_294
            (coe
               MAlonzo.Code.Once.Spec.Context.C__'8759'__52
               (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
               (coe
                  MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
                  (MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))))
            (coe
               MAlonzo.Code.Once.Spec.Context.C__'8759'__52
               (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
               (coe
                  MAlonzo.Code.Once.Spec.Context.C__'8759'__52
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_One_12)
                  (MAlonzo.Code.Once.Spec.Context.d_zeroUsage_56 (coe v0))))
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) v1
            (coe
               MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'fst_358 v1
               (coe
                  MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
                  (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_eff_32))
                  (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)))
            (coe
               MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'snd_374
               (coe
                  MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 (coe v1)
                  (coe
                     MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_eff_32))
                  (coe v2))
               (coe
                  MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
                  (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
                  (MAlonzo.Code.Once.Spec.Type.Sub.d_pure'8849'_18
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_eff_32))
                  (coe MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'var_252)))))
-- Once.Spec.Core.DerivedTyping.⊢outEffᶜ
d_'8866'outEff'7580'_838 ::
  MAlonzo.Code.Once.Spec.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
d_'8866'outEff'7580'_838 ~v0 ~v1 ~v2 v3 v4
  = du_'8866'outEff'7580'_838 v3 v4
du_'8866'outEff'7580'_838 ::
  MAlonzo.Code.Once.Spec.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Spec.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Spec.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__244
du_'8866'outEff'7580'_838 v0 v1
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
-- Once.Spec.Core.DerivedTyping.⊢effAppᶜ
d_'8866'effApp'7580'_858 ::
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
d_'8866'effApp'7580'_858 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11
                         v12
  = du_'8866'effApp'7580'_858 v4 v5 v6 v7 v8 v9 v10 v11 v12
du_'8866'effApp'7580'_858 ::
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
du_'8866'effApp'7580'_858 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'lam_272
      (MAlonzo.Code.Once.Spec.Type.Grade.d__'43'q__16
         (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)
         (coe
            MAlonzo.Code.Once.Spec.Type.Grade.d__'42'q__20
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10)))
      (coe
         MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'app_294
         (coe
            MAlonzo.Code.Once.Spec.Context.C__'8759'__52
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10) v1)
         (coe
            MAlonzo.Code.Once.Spec.Context.C__'8759'__52
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Zero_10) v2)
         (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14) v3
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
            (coe MAlonzo.Code.Once.Spec.Type.Sub.C_'8849''45'pe_14)
            (coe
               du_wk'45''8866''8242'_548 (coe v0) (coe v1) (coe v5)
               (coe
                  MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__28 (coe v3)
                  (coe
                     MAlonzo.Code.Once.Spec.Type.Grade.C_mk'45'kind_48
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_Many_14)
                     (coe MAlonzo.Code.Once.Spec.Type.Grade.C_eff_32))
                  (coe v4))
               (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
               (coe MAlonzo.Code.Once.Spec.Type.C_Unit_20) (coe v7)))
         (coe
            MAlonzo.Code.Once.Spec.Core.Typing.C_'8866'sub'45'eff_618
            (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
            (coe MAlonzo.Code.Once.Spec.Type.Sub.C_'8849''45'pe_14)
            (coe
               du_wk'45''8866''8242'_548 (coe v0) (coe v2) (coe v6) (coe v3)
               (coe MAlonzo.Code.Once.Spec.Type.Grade.C_pure_30)
               (coe MAlonzo.Code.Once.Spec.Type.C_Unit_20) (coe v8))))
