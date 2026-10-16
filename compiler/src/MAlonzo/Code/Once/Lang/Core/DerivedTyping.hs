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
d_ana'7580'_370 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_ana'7580'_370 ~v0 ~v1 ~v2 = du_ana'7580'_370
du_ana'7580'_370 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_ana'7580'_370 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Lang.Core.Derived.du_ana'7580'_410 v1 v2 v3 v4
-- Once.Lang.Core.DerivedTyping._.caseᶜ
d_case'7580'_376 ::
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
d_case'7580'_376 ~v0 ~v1 ~v2 = du_case'7580'_376
du_case'7580'_376 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_case'7580'_376 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Lang.Core.Derived.du_case'7580'_372 v1 v2 v3 v4
      v5
-- Once.Lang.Core.DerivedTyping._.composeᶜ
d_compose'7580'_380 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_compose'7580'_380 ~v0 ~v1 ~v2 = du_compose'7580'_380
du_compose'7580'_380 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_compose'7580'_380 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Lang.Core.Derived.du_compose'7580'_348 v1 v2 v3
      v4
-- Once.Lang.Core.DerivedTyping._.effAppᶜ
d_effApp'7580'_384 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_effApp'7580'_384 ~v0 ~v1 ~v2 = du_effApp'7580'_384
du_effApp'7580'_384 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_effApp'7580'_384 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Core.Derived.du_effApp'7580'_422 v1 v2 v3
-- Once.Lang.Core.DerivedTyping._.fstᶜ
d_fst'7580'_386 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_fst'7580'_386 ~v0 ~v1 ~v2 = du_fst'7580'_386
du_fst'7580'_386 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_fst'7580'_386 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Core.Derived.du_fst'7580'_280 v1 v2 v3
-- Once.Lang.Core.DerivedTyping._.idᶜ
d_id'7580'_388 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_id'7580'_388 ~v0 ~v1 ~v2 = du_id'7580'_388
du_id'7580'_388 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_id'7580'_388 v0 v1 v2
  = coe MAlonzo.Code.Once.Lang.Core.Derived.du_id'7580'_264 v1 v2
-- Once.Lang.Core.DerivedTyping._.inlᶜ
d_inl'7580'_392 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_inl'7580'_392 ~v0 ~v1 ~v2 = du_inl'7580'_392
du_inl'7580'_392 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_inl'7580'_392 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Core.Derived.du_inl'7580'_288 v1 v2 v3
-- Once.Lang.Core.DerivedTyping._.inrᶜ
d_inr'7580'_394 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_inr'7580'_394 ~v0 ~v1 ~v2 = du_inr'7580'_394
du_inr'7580'_394 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_inr'7580'_394 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Core.Derived.du_inr'7580'_292 v1 v2 v3
-- Once.Lang.Core.DerivedTyping._.inᶜ
d_in'7580'_396 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_in'7580'_396 ~v0 ~v1 ~v2 = du_in'7580'_396
du_in'7580'_396 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_in'7580'_396 v0 v1
  = coe MAlonzo.Code.Once.Lang.Core.Derived.du_in'7580'_336 v1
-- Once.Lang.Core.DerivedTyping._.outᶜ
d_out'7580'_400 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_out'7580'_400 ~v0 ~v1 ~v2 = du_out'7580'_400
du_out'7580'_400 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_out'7580'_400 v0 v1
  = coe MAlonzo.Code.Once.Lang.Core.Derived.du_out'7580'_340 v1
-- Once.Lang.Core.DerivedTyping._.pairᶜ
d_pair'7580'_402 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_pair'7580'_402 ~v0 ~v1 ~v2 = du_pair'7580'_402
du_pair'7580'_402 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_pair'7580'_402 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Lang.Core.Derived.du_pair'7580'_360 v1 v2 v3 v4
-- Once.Lang.Core.DerivedTyping._.sndᶜ
d_snd'7580'_404 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_snd'7580'_404 ~v0 ~v1 ~v2 = du_snd'7580'_404
du_snd'7580'_404 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_snd'7580'_404 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Core.Derived.du_snd'7580'_284 v1 v2 v3
-- Once.Lang.Core.DerivedTyping._.terminalᶜ
d_terminal'7580'_406 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
d_terminal'7580'_406 ~v0 ~v1 ~v2 = du_terminal'7580'_406
du_terminal'7580'_406 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62
du_terminal'7580'_406 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Core.Derived.du_terminal'7580'_268 v1 v2
-- Once.Lang.Core.DerivedTyping.⊢var′
d_'8866'var'8242'_416 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'var'8242'_416 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8866'var'8242'_416 v5
du_'8866'var'8242'_416 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'var'8242'_416 v0
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v0
      (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)
-- Once.Lang.Core.DerivedTyping.⊢idᶜ
d_'8866'id'7580'_430 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'id'7580'_430 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8866'id'7580'_430 v5
du_'8866'id'7580'_430 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'id'7580'_430 v0
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v0
         (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256))
-- Once.Lang.Core.DerivedTyping.⊢fstᶜ
d_'8866'fst'7580'_444 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'fst'7580'_444 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6
  = du_'8866'fst'7580'_444 v4 v6
du_'8866'fst'7580'_444 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'fst'7580'_444 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v1
         (coe
            MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'fst_370 v0
            (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)))
-- Once.Lang.Core.DerivedTyping.⊢sndᶜ
d_'8866'snd'7580'_458 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'snd'7580'_458 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6
  = du_'8866'snd'7580'_458 v3 v6
du_'8866'snd'7580'_458 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'snd'7580'_458 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v1
         (coe
            MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'snd_386 v0
            (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)))
-- Once.Lang.Core.DerivedTyping.⊢inlᶜ
d_'8866'inl'7580'_472 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'inl'7580'_472 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8866'inl'7580'_472 v6
du_'8866'inl'7580'_472 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'inl'7580'_472 v0
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v0
         (coe
            MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'inl_402
            (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)))
-- Once.Lang.Core.DerivedTyping.⊢inrᶜ
d_'8866'inr'7580'_486 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'inr'7580'_486 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8866'inr'7580'_486 v6
du_'8866'inr'7580'_486 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'inr'7580'_486 v0
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v0
         (coe
            MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'inr_418
            (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)))
-- Once.Lang.Core.DerivedTyping.⊢terminalᶜ
d_'8866'terminal'7580'_498 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'terminal'7580'_498 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8866'terminal'7580'_498 v5
du_'8866'terminal'7580'_498 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'terminal'7580'_498 v0
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10)
      (coe
         MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v0
         (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'unit_332))
-- Once.Lang.Core.DerivedTyping.⊢initialᶜ
d_'8866'initial'7580'_510 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'initial'7580'_510 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8866'initial'7580'_510 v5
du_'8866'initial'7580'_510 ::
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'initial'7580'_510 v0
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v0
         (coe
            MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'absurd_462
            (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)))
-- Once.Lang.Core.DerivedTyping.z+qz
d_z'43'qz_518 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_z'43'qz_518 = erased
-- Once.Lang.Core.DerivedTyping.z⊔z
d_z'8852'z_526 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_z'8852'z_526 = erased
-- Once.Lang.Core.DerivedTyping.arms
d_arms_542 ::
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
d_arms_542 = erased
-- Once.Lang.Core.DerivedTyping.wk-⊢′
d_wk'45''8866''8242'_564 ::
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
d_wk'45''8866''8242'_564 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9 v10
  = du_wk'45''8866''8242'_564 v4 v5 v6 v7 v9 v10
du_wk'45''8866''8242'_564 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Core.Syntax.T_Tm_62 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_wk'45''8866''8242'_564 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Lang.Core.Rename.du_wk'45''8866'_984 (coe v0)
      (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
-- Once.Lang.Core.DerivedTyping.⊢composeᶜ
d_'8866'compose'7580'_600 ::
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
d_'8866'compose'7580'_600 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                          ~v12 ~v13 v14 v15 v16 v17
  = du_'8866'compose'7580'_600
      v3 v4 v5 v6 v7 v8 v9 v10 v11 v14 v15 v16 v17
du_'8866'compose'7580'_600 ::
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
du_'8866'compose'7580'_600 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
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
            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
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
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
            (coe v5))
         (coe
            du_wk'45''8866''8242'_564 (coe v1) (coe v3) (coe v9)
            (coe
               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
               (coe
                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
               (coe v5))
            (coe
               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v5)
               (coe
                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
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
               MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
               (MAlonzo.Code.Once.Lang.Type.Grade.d__'183'p__44 (coe v8) (coe v7))
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
d_'8866'pair'7580'_650 ::
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
d_'8866'pair'7580'_650 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
                       ~v12 ~v13 v14 v15 v16 v17
  = du_'8866'pair'7580'_650
      v3 v4 v5 v6 v7 v8 v9 v10 v11 v14 v15 v16 v17
du_'8866'pair'7580'_650 ::
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
du_'8866'pair'7580'_650 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
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
            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
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
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
            (coe v6))
         (coe
            du_wk'45''8866''8242'_564 (coe v1) (coe v3) (coe v9)
            (coe
               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
               (coe
                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v8))
               (coe v6))
            (coe
               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
               (coe
                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
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
               MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
               (MAlonzo.Code.Once.Lang.Type.Grade.d__'183'p__44 (coe v7) (coe v8))
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
                  (MAlonzo.Code.Once.Lang.Type.Grade.d__'183'p__44
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
                     (coe
                        MAlonzo.Code.Once.Lang.Type.Grade.d__'183'p__44
                        (coe
                           MAlonzo.Code.Once.Lang.Type.Grade.d_positionGrade_54
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
d_'8866'case'7580'_688 ::
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
d_'8866'case'7580'_688 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 ~v11
                       v12 v13 v14
  = du_'8866'case'7580'_688 v3 v4 v5 v6 v7 v8 v9 v10 v12 v13 v14
du_'8866'case'7580'_688 ::
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
du_'8866'case'7580'_688 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
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
            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
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
               MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v7))
            (coe v6))
         (coe
            du_wk'45''8866''8242'_564 (coe v1) (coe v3) (coe v8)
            (coe
               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v5)
               (coe
                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v7))
               (coe v6))
            (coe
               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
               (coe
                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
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
               MAlonzo.Code.Once.Lang.Core.Typing.du_'8866'case'8852'_726
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
d_'8866'curry'7580'_726 ::
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
d_'8866'curry'7580'_726 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 v8 ~v9 v10 ~v11
                        v12 v13
  = du_'8866'curry'7580'_726 v3 v5 v6 v7 v8 v10 v12 v13
du_'8866'curry'7580'_726 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'curry'7580'_726 v0 v1 v2 v3 v4 v5 v6 v7
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
            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
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
            MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
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
d_'8866'cata'7580'_760 ::
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
d_'8866'cata'7580'_760 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 v8 ~v9 v10 v11
                       v12
  = du_'8866'cata'7580'_760 v3 v5 v6 v7 v8 v10 v11 v12
du_'8866'cata'7580'_760 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Sub.T__'8849'π__8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'cata'7580'_760 v0 v1 v2 v3 v4 v5 v6 v7
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
            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
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
d_'8866'ana'7580'_796 ::
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
d_'8866'ana'7580'_796 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 ~v8 v9 v10 v11 v12
                      v13
  = du_'8866'ana'7580'_796 v3 v4 v5 v6 v7 v9 v10 v11 v12 v13
du_'8866'ana'7580'_796 ::
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
du_'8866'ana'7580'_796 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'sub'45'eff_678
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
               du_wk'45''8866''8242'_564 (coe v1) (coe v2) (coe v6)
               (coe
                  MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
                  (coe
                     MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v5))
                  (coe
                     MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v3)
                     (coe v4)))
               (coe v4) (coe v9))
            (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)))
-- Once.Lang.Core.DerivedTyping.⊢applyᶜ
d_'8866'apply'7580'_822 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'apply'7580'_822 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_'8866'apply'7580'_822 v3 v5 v6
du_'8866'apply'7580'_822 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'apply'7580'_822 v0 v1 v2
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
                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
               (coe v2))
            (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256)))
-- Once.Lang.Core.DerivedTyping.⊢inᶜ
d_'8866'in'7580'_834 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'in'7580'_834 ~v0 ~v1 ~v2 ~v3 v4 = du_'8866'in'7580'_834 v4
du_'8866'in'7580'_834 ::
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'in'7580'_834 v0
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'roll_476 v0
         (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256))
-- Once.Lang.Core.DerivedTyping.⊢outᶜ
d_'8866'out'7580'_844 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'out'7580'_844 ~v0 ~v1 ~v2 v3 v4
  = du_'8866'out'7580'_844 v3 v4
du_'8866'out'7580'_844 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'out'7580'_844 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'lam_276
      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_One_12)
      (coe
         MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'out_540
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34)
         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34) v0 v1
         (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256))
-- Once.Lang.Core.DerivedTyping.⊢applyEffᶜ
d_'8866'applyEff'7580'_858 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'applyEff'7580'_858 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7
  = du_'8866'applyEff'7580'_858 v3 v5 v6 v7
du_'8866'applyEff'7580'_858 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'applyEff'7580'_858 v0 v1 v2 v3
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
                     MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                     (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v1))
                  (coe v3))
               (coe MAlonzo.Code.Once.Lang.Core.Typing.C_'8866'var_256))))
-- Once.Lang.Core.DerivedTyping.⊢outEffᶜ
d_'8866'outEff'7580'_872 ::
  MAlonzo.Code.Once.Lang.Core.PolyTy.T_Sig_826 ->
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
d_'8866'outEff'7580'_872 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'8866'outEff'7580'_872 v3 v4 v5
du_'8866'outEff'7580'_872 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Core.Typing.T__'8866''91'_'93'_'8759'_'33'__248
du_'8866'outEff'7580'_872 v0 v1 v2
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
d_'8866'effApp'7580'_894 ::
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
d_'8866'effApp'7580'_894 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11
                         v12 v13
  = du_'8866'effApp'7580'_894 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
du_'8866'effApp'7580'_894 ::
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
du_'8866'effApp'7580'_894 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
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
            du_wk'45''8866''8242'_564 (coe v0) (coe v1) (coe v6)
            (coe
               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v4)
               (coe
                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v3))
               (coe v5))
            (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20) (coe v8))
         (coe
            du_wk'45''8866''8242'_564 (coe v0) (coe v2) (coe v7) (coe v4)
            (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20) (coe v9)))
