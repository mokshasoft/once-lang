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

module MAlonzo.Code.Once.Lang.Core.DerivedTyping where

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
import qualified MAlonzo.Code.Once.Lang.Core.Derived
import qualified MAlonzo.Code.Once.Lang.Core.PolyTy
import qualified MAlonzo.Code.Once.Lang.Core.Rename
import qualified MAlonzo.Code.Once.Lang.Core.Syntax
import qualified MAlonzo.Code.Once.Lang.Core.Typing
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Sub
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Name

-- Once.Lang.Core.DerivedTyping._.Tm
d_Tm_30 a0 a1 a2 a3 = ()
-- Once.Lang.Core.DerivedTyping._.wk
d_wk_144 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_wk_144 ~v0 ~v1 ~v2 = du_wk_144
du_wk_144 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_wk_144 v0 = coe MAlonzo.Code.Once.Lang.Core.Syntax.du_wk_274
-- Once.Lang.Core.DerivedTyping._._⊢[_]_∷_!_
d__'8866''91'_'93'_'8759'_'33'__252 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Once.Lang.Core.DerivedTyping._.anaᶜ
d_ana'7580'_366 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_ana'7580'_366 ~v0 ~v1 ~v2 = du_ana'7580'_366
du_ana'7580'_366 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_ana'7580'_366 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Lang.Core.Derived.du_ana'7580'_410 v1 v2 v3 v4
-- Once.Lang.Core.DerivedTyping._.caseᶜ
d_case'7580'_372 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_case'7580'_372 ~v0 ~v1 ~v2 = du_case'7580'_372
du_case'7580'_372 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_case'7580'_372 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Lang.Core.Derived.du_case'7580'_372 v1 v2 v3 v4
      v5
-- Once.Lang.Core.DerivedTyping._.composeᶜ
d_compose'7580'_376 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_compose'7580'_376 ~v0 ~v1 ~v2 = du_compose'7580'_376
du_compose'7580'_376 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_compose'7580'_376 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Lang.Core.Derived.du_compose'7580'_348 v1 v2 v3
      v4
-- Once.Lang.Core.DerivedTyping._.effAppᶜ
d_effApp'7580'_380 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_effApp'7580'_380 ~v0 ~v1 ~v2 = du_effApp'7580'_380
du_effApp'7580'_380 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_effApp'7580'_380 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Core.Derived.du_effApp'7580'_430 v1 v2 v3
-- Once.Lang.Core.DerivedTyping._.fstᶜ
d_fst'7580'_382 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_fst'7580'_382 ~v0 ~v1 ~v2 = du_fst'7580'_382
du_fst'7580'_382 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_fst'7580'_382 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Core.Derived.du_fst'7580'_280 v1 v2 v3
-- Once.Lang.Core.DerivedTyping._.idᶜ
d_id'7580'_384 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_id'7580'_384 ~v0 ~v1 ~v2 = du_id'7580'_384
du_id'7580'_384 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_id'7580'_384 v0 v1 v2
  = coe MAlonzo.Code.Once.Lang.Core.Derived.du_id'7580'_264 v1 v2
-- Once.Lang.Core.DerivedTyping._.inlᶜ
d_inl'7580'_388 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_inl'7580'_388 ~v0 ~v1 ~v2 = du_inl'7580'_388
du_inl'7580'_388 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_inl'7580'_388 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Core.Derived.du_inl'7580'_288 v1 v2 v3
-- Once.Lang.Core.DerivedTyping._.inrᶜ
d_inr'7580'_390 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_inr'7580'_390 ~v0 ~v1 ~v2 = du_inr'7580'_390
du_inr'7580'_390 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_inr'7580'_390 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Core.Derived.du_inr'7580'_292 v1 v2 v3
-- Once.Lang.Core.DerivedTyping._.inᶜ
d_in'7580'_392 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_in'7580'_392 ~v0 ~v1 ~v2 = du_in'7580'_392
du_in'7580'_392 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_in'7580'_392 v0 v1
  = coe MAlonzo.Code.Once.Lang.Core.Derived.du_in'7580'_336 v1
-- Once.Lang.Core.DerivedTyping._.outᶜ
d_out'7580'_398 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_out'7580'_398 ~v0 ~v1 ~v2 = du_out'7580'_398
du_out'7580'_398 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_out'7580'_398 v0 v1
  = coe MAlonzo.Code.Once.Lang.Core.Derived.du_out'7580'_340 v1
-- Once.Lang.Core.DerivedTyping._.pairᶜ
d_pair'7580'_400 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_pair'7580'_400 ~v0 ~v1 ~v2 = du_pair'7580'_400
du_pair'7580'_400 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_pair'7580'_400 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Lang.Core.Derived.du_pair'7580'_360 v1 v2 v3 v4
-- Once.Lang.Core.DerivedTyping._.sndᶜ
d_snd'7580'_402 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_snd'7580'_402 ~v0 ~v1 ~v2 = du_snd'7580'_402
du_snd'7580'_402 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_snd'7580'_402 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Core.Derived.du_snd'7580'_284 v1 v2 v3
-- Once.Lang.Core.DerivedTyping._.terminalᶜ
d_terminal'7580'_404 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_terminal'7580'_404 ~v0 ~v1 ~v2 = du_terminal'7580'_404
du_terminal'7580'_404 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_terminal'7580'_404 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Core.Derived.du_terminal'7580'_268 v1 v2
-- Once.Lang.Core.DerivedTyping.⊢var′
d_'8866'var'8242'_414 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'var'8242'_414 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8866'var'8242'_414 v5
du_'8866'var'8242'_414 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'var'8242'_414 v0
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_662
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v0
      (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)
-- Once.Lang.Core.DerivedTyping.⊢idᶜ
d_'8866'id'7580'_428 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'id'7580'_428 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8866'id'7580'_428 v5
du_'8866'id'7580'_428 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'id'7580'_428 v0
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_662
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v0
         (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256))
-- Once.Lang.Core.DerivedTyping.⊢fstᶜ
d_'8866'fst'7580'_442 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'fst'7580'_442 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6
  = du_'8866'fst'7580'_442 v4 v6
du_'8866'fst'7580'_442 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'fst'7580'_442 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_662
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v1
         (coe
            MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'fst_370 v0
            (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)))
-- Once.Lang.Core.DerivedTyping.⊢sndᶜ
d_'8866'snd'7580'_456 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'snd'7580'_456 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
  = du_'8866'snd'7580'_456 v3 v6
du_'8866'snd'7580'_456 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'snd'7580'_456 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_662
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v1
         (coe
            MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'snd_386 v0
            (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)))
-- Once.Lang.Core.DerivedTyping.⊢inlᶜ
d_'8866'inl'7580'_470 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'inl'7580'_470 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8866'inl'7580'_470 v6
du_'8866'inl'7580'_470 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'inl'7580'_470 v0
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_662
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v0
         (coe
            MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'inl_402
            (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)))
-- Once.Lang.Core.DerivedTyping.⊢inrᶜ
d_'8866'inr'7580'_484 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'inr'7580'_484 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8866'inr'7580'_484 v6
du_'8866'inr'7580'_484 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'inr'7580'_484 v0
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_662
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v0
         (coe
            MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'inr_418
            (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)))
-- Once.Lang.Core.DerivedTyping.⊢terminalᶜ
d_'8866'terminal'7580'_496 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'terminal'7580'_496 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8866'terminal'7580'_496 v5
du_'8866'terminal'7580'_496 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'terminal'7580'_496 v0
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
      (coe
         MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_662
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v0
         (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'unit_332))
-- Once.Lang.Core.DerivedTyping.⊢initialᶜ
d_'8866'initial'7580'_508 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'initial'7580'_508 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8866'initial'7580'_508 v5
du_'8866'initial'7580'_508 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'initial'7580'_508 v0
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_662
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v0
         (coe
            MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'absurd_462
            (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)))
-- Once.Lang.Core.DerivedTyping.z+qz
d_z'43'qz_516 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_z'43'qz_516 = erased
-- Once.Lang.Core.DerivedTyping.z⊔z
d_z'8852'z_524 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_z'8852'z_524 = erased
-- Once.Lang.Core.DerivedTyping.arms
d_arms_540 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_arms_540 = erased
-- Once.Lang.Core.DerivedTyping.wk-⊢′
d_wk'45''8866''8242'_562 ::
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
d_wk'45''8866''8242'_562 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9 v10
  = du_wk'45''8866''8242'_562 v4 v5 v6 v7 v9 v10
du_wk'45''8866''8242'_562 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_wk'45''8866''8242'_562 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Lang.Core.Rename.du_wk'45''8866'_964 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
-- Once.Lang.Core.DerivedTyping.⊢composeᶜ
d_'8866'compose'7580'_598 ::
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
d_'8866'compose'7580'_598 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                          ~v12 ~v13 v14 v15 v16 v17
  = du_'8866'compose'7580'_598
      v3 v4 v5 v6 v7 v8 v9 v10 v11 v14 v15 v16 v17
du_'8866'compose'7580'_598 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'compose'7580'_598 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                           v12
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'let_326 v2
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
            (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
               (coe
                  MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                  (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))
                  (coe
                     MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                     (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))))))
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v3)))
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v5)
         (coe
            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v7))
         (coe v6))
      v11
      (coe
         MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'let_326
         (coe
            MAlonzo.Code.Once.Lang.Context.C__'8759'__52
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10) v3)
         (coe
            MAlonzo.Code.Once.Lang.Context.C__'8759'__52
            (MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
               (coe
                  MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)))))
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
               (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))
               (coe
                  MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                  (coe
                     MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                     (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))
                     (coe
                        MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                        (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0)))))))
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
            (coe v5))
         (coe
            du_wk'45''8866''8242'_562 (coe v1) (coe v3) (coe v9)
            (coe
               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
               (coe
                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
               (coe v5))
            (coe
               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v5)
               (coe
                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v7))
               (coe v6))
            (coe v12))
         (coe
            MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
            (MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
               (coe
                  MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)))))
            (coe
               MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_662
               (MAlonzo.Code.Once.Lang.Type.Grade.d__'183'p__52 (coe v8) (coe v7))
               v10
               (coe
                  MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'app_302
                  (coe
                     MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                     (coe
                        MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                        (coe
                           MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                           (MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0)))))
                  (coe
                     MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                     (MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                        (coe
                           MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)))
                     (coe
                        MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                        (MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                           (coe
                              MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)))
                        (coe
                           MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                           (MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)))
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                              (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))
                              (coe
                                 MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                 (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0)))))))
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) v7
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v8 v5
                  (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)
                  (coe
                     MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'app_302
                     (coe
                        MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                        (coe
                           MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                              (MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0)))))
                     (coe
                        MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                        (coe
                           MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                              (MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0)))))
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) v8
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v4
                     (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)
                     (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256))))))
-- Once.Lang.Core.DerivedTyping.⊢pairᶜ
d_'8866'pair'7580'_648 ::
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
d_'8866'pair'7580'_648 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                       ~v12 ~v13 v14 v15 v16 v17
  = du_'8866'pair'7580'_648
      v3 v4 v5 v6 v7 v8 v9 v10 v11 v14 v15 v16 v17
du_'8866'pair'7580'_648 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'pair'7580'_648 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'let_326 v2
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
               (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))
               (coe
                  MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                  (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))))
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
               (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))
               (coe
                  MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                  (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0)))))
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12) (coe v3)))
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
         (coe
            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v7))
         (coe v5))
      v11
      (coe
         MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'let_326
         (coe
            MAlonzo.Code.Once.Lang.Context.C__'8759'__52
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10) v3)
         (coe
            MAlonzo.Code.Once.Lang.Context.C__'8759'__52
            (MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
               (coe
                  MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)))
               (coe
                  MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10))))
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
               (coe
                  MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                  (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))
                  (coe
                     MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                     (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))))
               (coe
                  MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                  (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))
                  (coe
                     MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                     (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))))))
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
            (coe v6))
         (coe
            du_wk'45''8866''8242'_562 (coe v1) (coe v3) (coe v9)
            (coe
               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
               (coe
                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
               (coe v6))
            (coe
               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
               (coe
                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v7))
               (coe v5))
            (coe v12))
         (coe
            MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
            (MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
               (coe
                  MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)))
               (coe
                  MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12))))
            (coe
               MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_662
               (MAlonzo.Code.Once.Lang.Type.Grade.d__'183'p__52 (coe v7) (coe v8))
               v10
               (coe
                  MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'pair_354
                  (coe
                     MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                     (MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                        (coe
                           MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)))
                     (coe
                        MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                        (MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                           (coe
                              MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)))
                        (coe
                           MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                           (MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)))
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                              (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))
                              (coe
                                 MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                 (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0)))))))
                  (coe
                     MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                     (MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                        (coe
                           MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)))
                     (coe
                        MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                        (coe
                           MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                           (MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)))
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                              (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))
                              (coe
                                 MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                 (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0)))))))
                  (MAlonzo.Code.Once.Lang.Type.Grade.d__'183'p__52
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Grade.d__'183'p__52
                        (coe
                           MAlonzo.Code.Once.Lang.Type.Grade.d_positionGrade_62
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                        (coe v7)))
                  v8
                  (coe
                     MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'app_302
                     (coe
                        MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                        (coe
                           MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                              (MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0)))))
                     (coe
                        MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                        (coe
                           MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                              (MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0)))))
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) v7
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v4
                     (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)
                     (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256))
                  (coe
                     MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'app_302
                     (coe
                        MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                        (coe
                           MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                              (MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0)))))
                     (coe
                        MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                        (coe
                           MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                              (MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0)))))
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) v8
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v4
                     (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)
                     (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256))))))
-- Once.Lang.Core.DerivedTyping.⊢caseᶜ
d_'8866'case'7580'_686 ::
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
d_'8866'case'7580'_686 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11
                       v12 v13 v14
  = du_'8866'case'7580'_686 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v14
du_'8866'case'7580'_686 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'case'7580'_686 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'let_326 v2
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
            (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100
               (coe
                  MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                  (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))
                  (coe
                     MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                     (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))))
               (coe
                  MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                  (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))
                  (coe
                     MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                     (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))))))
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12) (coe v3)))
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
         (coe
            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v7))
         (coe v6))
      v9
      (coe
         MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'let_326
         (coe
            MAlonzo.Code.Once.Lang.Context.C__'8759'__52
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10) v3)
         (coe
            MAlonzo.Code.Once.Lang.Context.C__'8759'__52
            (MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
               (coe
                  MAlonzo.Code.Once.Lang.Type.Grade.d__'8852'q__22
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)))
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)))))
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
               (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))
               (coe
                  MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100
                  (coe
                     MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                     (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))
                     (coe
                        MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                        (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))))
                  (coe
                     MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                     (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))
                     (coe
                        MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                        (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0)))))))
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
         (coe
            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v5)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v7))
            (coe v6))
         (coe
            du_wk'45''8866''8242'_562 (coe v1) (coe v3) (coe v8)
            (coe
               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v5)
               (coe
                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v7))
               (coe v6))
            (coe
               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
               (coe
                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v7))
               (coe v6))
            (coe v10))
         (coe
            MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
            (MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
               (coe
                  MAlonzo.Code.Once.Lang.Type.Grade.d__'8852'q__22
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)))
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)))))
            (coe
               MAlonzo.Code.Once.Lang.Core.Typing.du_'8866'case'8852'_710
               (coe
                  MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                  (coe
                     MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                     (coe
                        MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                        (MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0)))))
               (coe
                  MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                  (MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)))
                  (coe
                     MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                     (MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                        (coe
                           MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)))
                     (coe
                        MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                        (MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                           (coe
                              MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)))
                        (coe
                           MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                           (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                              (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0)))))))
               (coe
                  MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                  (MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)))
                  (coe
                     MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                     (coe
                        MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                        (MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                           (coe
                              MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)))
                        (coe
                           MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                           (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                              (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0)))))))
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) (coe v7) (coe v4)
               (coe v5) (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)
               (coe
                  MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'app_302
                  (coe
                     MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                     (coe
                        MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                        (coe
                           MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                              (MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))))))
                  (coe
                     MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                     (coe
                        MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                        (coe
                           MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                              (MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))))))
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) v7
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v4
                  (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)
                  (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256))
               (coe
                  MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'app_302
                  (coe
                     MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                     (coe
                        MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                        (coe
                           MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                              (MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))))))
                  (coe
                     MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                     (coe
                        MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                        (coe
                           MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                              (MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))))))
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) v7
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v5
                  (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)
                  (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)))))
-- Once.Lang.Core.DerivedTyping.⊢curryᶜ
d_'8866'curry'7580'_724 ::
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
d_'8866'curry'7580'_724 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 v8 ~v9 v10 ~v11
                        v12 v13
  = du_'8866'curry'7580'_724 v3 v5 v6 v7 v8 v10 v12 v13
du_'8866'curry'7580'_724 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'curry'7580'_724 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'let_326 v1
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
         (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
            (coe
               MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
               (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))
               (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0)))))
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
         (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v2) (coe v3))
         (coe
            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
         (coe v4))
      v7
      (coe
         MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
         (MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
               (coe
                  MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10))))
         (coe
            MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_662
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v6
            (coe
               MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
               (MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12))))
               (coe
                  MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'app_302
                  (coe
                     MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                     (coe
                        MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                        (coe
                           MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                           (MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0)))))
                  (coe
                     MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                     (MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12))
                     (coe
                        MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                        (MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10))
                        (coe
                           MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                           (MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10))
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                              (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))
                              (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))))))
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) v5
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                  (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v2) (coe v3))
                  (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)
                  (coe
                     MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'pair_354
                     (coe
                        MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                        (coe
                           MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                              (MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0)))))
                     (coe
                        MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                        (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                        (coe
                           MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                              (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                              (MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0)))))
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                     (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)
                     (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256))))))
-- Once.Lang.Core.DerivedTyping.⊢cataᶜ
d_'8866'cata'7580'_758 ::
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
d_'8866'cata'7580'_758 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 v8 ~v9 v10 v11
                       v12
  = du_'8866'cata'7580'_758 v3 v5 v6 v7 v8 v10 v11 v12
du_'8866'cata'7580'_758 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'cata'7580'_758 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'let_326 v1
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
            (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0)))
         (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0)))
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
         (coe
            MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v2)
            (coe v3))
         (coe
            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v4))
         (coe v3))
      v7
      (coe
         MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
         (MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10))
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12))
         (coe
            MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'fold_500
            (coe
               MAlonzo.Code.Once.Lang.Context.C__'8759'__52
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
               (coe
                  MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                  (MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))))
            (coe
               MAlonzo.Code.Once.Lang.Context.C__'8759'__52
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
               (coe
                  MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                  (MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))))
            v4 (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v5 v6
            (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)
            (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)))
-- Once.Lang.Core.DerivedTyping.⊢anaᶜ
d_'8866'ana'7580'_794 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'ana'7580'_794 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 ~v8 v9 v10 v11 v12
                      v13
  = du_'8866'ana'7580'_794 v3 v4 v5 v6 v7 v9 v10 v11 v12 v13
du_'8866'ana'7580'_794 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'ana'7580'_794 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_662
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v7
         (coe
            MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'unfold_524
            (coe
               MAlonzo.Code.Once.Lang.Context.C__'8759'__52
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10) v2)
            (coe
               MAlonzo.Code.Once.Lang.Context.C__'8759'__52
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
               (MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0)))
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v4 v8
            (coe
               du_wk'45''8866''8242'_562 (coe v1) (coe v2) (coe v6)
               (coe
                  MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.d_fin_46 (coe v5)))
                  (coe
                     MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v3)
                     (coe v4)))
               (coe v4) (coe v9))
            (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)))
-- Once.Lang.Core.DerivedTyping.⊢loopᶜ
d_'8866'loop'7580'_824 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'loop'7580'_824 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 ~v8 v9
  = du_'8866'loop'7580'_824 v3 v5 v6 v7 v9
du_'8866'loop'7580'_824 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'loop'7580'_824 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'let_326 v1
      (coe
         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
         (coe
            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
            (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0)))
         (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0)))
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
      (coe
         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v2)
         (coe
            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_36))
         (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v3) (coe v2)))
      v4
      (coe
         MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
         (MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10))
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12))
         (coe
            MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'iter_562
            (coe
               MAlonzo.Code.Once.Lang.Context.C__'8759'__52
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
               (coe
                  MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                  (MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))))
            (coe
               MAlonzo.Code.Once.Lang.Context.C__'8759'__52
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
               (coe
                  MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
                  (MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))))
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v2
            (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)
            (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)))
-- Once.Lang.Core.DerivedTyping.⊢applyᶜ
d_'8866'apply'7580'_846 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'apply'7580'_846 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_'8866'apply'7580'_846 v3 v5 v6
du_'8866'apply'7580'_846 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'apply'7580'_846 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
      (MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
         (coe
            MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)))
      (coe
         MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'app_302
         (coe
            MAlonzo.Code.Once.Lang.Context.C__'8759'__52
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
            (MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0)))
         (coe
            MAlonzo.Code.Once.Lang.Context.C__'8759'__52
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
            (MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0)))
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v1
         (coe
            MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'fst_370 v1
            (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256))
         (coe
            MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'snd_386
            (coe
               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v1)
               (coe
                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
               (coe v2))
            (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)))
-- Once.Lang.Core.DerivedTyping.⊢inᶜ
d_'8866'in'7580'_858 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'in'7580'_858 ~v0 ~v1 ~v2 ~v3 v4 = du_'8866'in'7580'_858 v4
du_'8866'in'7580'_858 ::
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'in'7580'_858 v0
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'roll_476 v0
         (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256))
-- Once.Lang.Core.DerivedTyping.⊢outᶜ
d_'8866'out'7580'_868 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'out'7580'_868 ~v0 ~v1 ~v2 v3 v4
  = du_'8866'out'7580'_868 v3 v4
du_'8866'out'7580'_868 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'out'7580'_868 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'out_540
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_42)
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v0 v1
         (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256))
-- Once.Lang.Core.DerivedTyping.⊢applyEffᶜ
d_'8866'applyEff'7580'_882 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'applyEff'7580'_882 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7
  = du_'8866'applyEff'7580'_882 v3 v5 v6 v7
du_'8866'applyEff'7580'_882 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'applyEff'7580'_882 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
      (MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
         (coe
            MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)))
      (coe
         MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
         (MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
            (coe
               MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)))
         (coe
            MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'app_302
            (coe
               MAlonzo.Code.Once.Lang.Context.C__'8759'__52
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
               (coe
                  MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                  (MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))))
            (coe
               MAlonzo.Code.Once.Lang.Context.C__'8759'__52
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
               (coe
                  MAlonzo.Code.Once.Lang.Context.C__'8759'__52
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
                  (MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))))
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) v1
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v2
            (coe
               MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'fst_370 v2
               (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256))
            (coe
               MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'snd_386
               (coe
                  MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v2)
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v1))
                  (coe v3))
               (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256))))
-- Once.Lang.Core.DerivedTyping.⊢outEffᶜ
d_'8866'outEff'7580'_896 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'outEff'7580'_896 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'8866'outEff'7580'_896 v3 v4 v5
du_'8866'outEff'7580'_896 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Finite_40 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'outEff'7580'_896 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
         (coe
            MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'out_540 v0
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v1 v2
            (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)))
-- Once.Lang.Core.DerivedTyping.⊢effAppᶜ
d_'8866'effApp'7580'_918 ::
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
d_'8866'effApp'7580'_918 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11
                         v12 v13
  = du_'8866'effApp'7580'_918 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
du_'8866'effApp'7580'_918 ::
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
du_'8866'effApp'7580'_918 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
      (MAlonzo.Code.Once.Lang.Type.Grade.d__'43'q__16
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
         (coe
            MAlonzo.Code.Once.Lang.Type.Grade.d__'42'q__20
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)))
      (coe
         MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'app_302
         (coe
            MAlonzo.Code.Once.Lang.Context.C__'8759'__52
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10) v1)
         (coe
            MAlonzo.Code.Once.Lang.Context.C__'8759'__52
            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10) v2)
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) v3
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v4
         (coe
            du_wk'45''8866''8242'_562 (coe v0) (coe v1) (coe v6)
            (coe
               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
               (coe
                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_78
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v3))
               (coe v5))
            (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20) (coe v8))
         (coe
            du_wk'45''8866''8242'_562 (coe v0) (coe v2) (coe v7) (coe v4)
            (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20) (coe v9)))
