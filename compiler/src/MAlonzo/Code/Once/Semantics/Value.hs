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

module MAlonzo.Code.Once.Semantics.Value where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Type

-- Once.Semantics.Value.⟦μ⟧
d_'10214'μ'10215'_10 ::
  () -> () -> MAlonzo.Code.Once.Type.T_Functor_106 -> ()
d_'10214'μ'10215'_10 = erased
-- Once.Semantics.Value.⟦ν⟧
d_'10214'ν'10215'_12 ::
  () -> () -> MAlonzo.Code.Once.Type.T_Functor_106 -> ()
d_'10214'ν'10215'_12 = erased
-- Once.Semantics.Value.⟦_⟧
d_'10214'_'10215'_14 ::
  () -> () -> MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_'10214'_'10215'_14 = erased
-- Once.Semantics.Value.⟦_⟧ᵍ
d_'10214'_'10215''7501'_46 ::
  () -> () -> MAlonzo.Code.Once.Type.T_Type_108 -> ()
d_'10214'_'10215''7501'_46 = erased
-- Once.Semantics.Value.eraseᵍ
d_erase'7501'_92 ::
  () -> () -> MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_erase'7501'_92 ~v0 ~v1 v2 v3 = du_erase'7501'_92 v2 v3
du_erase'7501'_92 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
du_erase'7501'_92 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_120 -> coe v1
      MAlonzo.Code.Once.Type.C_Void_122 -> coe v1
      MAlonzo.Code.Once.Type.C__'42'__124 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_erase'7501'_92 (coe v2) (coe v4))
                    (coe du_erase'7501'_92 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'43'__126 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_erase'7501'_92 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_erase'7501'_92 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v2 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v5 v6
               -> coe
                    seq (coe v5)
                    (case coe v6 of
                       MAlonzo.Code.Once.Type.C_pure_34
                         -> coe
                              (\ v7 ->
                                 coe
                                   MAlonzo.Code.Once.Res.C_returns_12
                                   (coe du_erase'7501'_92 (coe v4) (coe v1 v7)))
                       MAlonzo.Code.Once.Type.C_eff_36
                         -> coe
                              (\ v7 ->
                                 coe
                                   MAlonzo.Code.Once.Res.du_mapRes_46
                                   (coe du_erase'7501'_92 (coe v4)) (coe v1 v7))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_130 v2 -> coe v1
      MAlonzo.Code.Once.Type.C_ν'45'type_132 v2 v3 -> coe v1
      MAlonzo.Code.Once.Type.C_Int_134 -> coe v1
      MAlonzo.Code.Once.Type.C_Float_136 -> coe v1
      MAlonzo.Code.Once.Type.C_rigid_138 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.⟦_⟧F
d_'10214'_'10215'F_186 ::
  () -> () -> MAlonzo.Code.Once.Type.T_Functor_106 -> () -> ()
d_'10214'_'10215'F_186 = erased
-- Once.Semantics.Value.sem-functor-coherence
d_sem'45'functor'45'coherence_210 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'functor'45'coherence_210 = erased
-- Once.Semantics.Value.coerce-functor
d_coerce'45'functor_250 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'functor_250 ~v0 ~v1 v2 ~v3 v4
  = du_coerce'45'functor_250 v2 v4
du_coerce'45'functor_250 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> AgdaAny -> AgdaAny
du_coerce'45'functor_250 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_112 v2 -> coe v1
      MAlonzo.Code.Once.Type.C_Id_114 -> coe v1
      MAlonzo.Code.Once.Type.C__'8853'__116 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coerce'45'functor_250 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coerce'45'functor_250 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__118 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coerce'45'functor_250 (coe v2) (coe v4))
                    (coe du_coerce'45'functor_250 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_292 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_292 ~v0 ~v1 v2 ~v3 v4
  = du_coerce'45'functor'8315''185'_292 v2 v4
du_coerce'45'functor'8315''185'_292 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> AgdaAny -> AgdaAny
du_coerce'45'functor'8315''185'_292 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_112 v2 -> coe v1
      MAlonzo.Code.Once.Type.C_Id_114 -> coe v1
      MAlonzo.Code.Once.Type.C__'8853'__116 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coerce'45'functor'8315''185'_292 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coerce'45'functor'8315''185'_292 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__118 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coerce'45'functor'8315''185'_292 (coe v2) (coe v4))
                    (coe du_coerce'45'functor'8315''185'_292 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.coerce-round-trip
d_coerce'45'round'45'trip_336 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'round'45'trip_336 = erased
-- Once.Semantics.Value.coerce⁻¹-round-trip
d_coerce'8315''185''45'round'45'trip_380 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'8315''185''45'round'45'trip_380 = erased
-- Once.Semantics.Value.coerce-struct
d_coerce'45'struct_422 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'struct_422 ~v0 ~v1 = du_coerce'45'struct_422
du_coerce'45'struct_422 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
du_coerce'45'struct_422 v0 v1 v2
  = coe du_coerce'45'functor_250 v0 v2
-- Once.Semantics.Value.coerce-struct⁻¹
d_coerce'45'struct'8315''185'_428 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'struct'8315''185'_428 ~v0 ~v1
  = du_coerce'45'struct'8315''185'_428
du_coerce'45'struct'8315''185'_428 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
du_coerce'45'struct'8315''185'_428 v0 v1 v2
  = coe du_coerce'45'functor'8315''185'_292 v0 v2
-- Once.Semantics.Value.coerce-struct-round-trip
d_coerce'45'struct'45'round'45'trip_436 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'45'round'45'trip_436 = erased
-- Once.Semantics.Value.coerce-struct⁻¹-round-trip
d_coerce'45'struct'8315''185''45'round'45'trip_444 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'8315''185''45'round'45'trip_444 = erased
-- Once.Semantics.Value.sem-fst
d_sem'45'fst_450 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'fst_450 ~v0 ~v1 ~v2 ~v3 v4 = du_sem'45'fst_450 v4
du_sem'45'fst_450 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_sem'45'fst_450 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)
-- Once.Semantics.Value.sem-snd
d_sem'45'snd_456 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'snd_456 ~v0 ~v1 ~v2 ~v3 v4 = du_sem'45'snd_456 v4
du_sem'45'snd_456 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_sem'45'snd_456 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)
-- Once.Semantics.Value.sem-pair
d_sem'45'pair_462 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'pair_462 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_sem'45'pair_462 v4 v5
du_sem'45'pair_462 ::
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sem'45'pair_462 v0 v1
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
-- Once.Semantics.Value.sem-inl
d_sem'45'inl_472 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inl_472 ~v0 ~v1 ~v2 ~v3 = du_sem'45'inl_472
du_sem'45'inl_472 ::
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sem'45'inl_472 = coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
-- Once.Semantics.Value.sem-inr
d_sem'45'inr_478 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inr_478 ~v0 ~v1 ~v2 ~v3 = du_sem'45'inr_478
du_sem'45'inr_478 ::
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sem'45'inr_478 = coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
-- Once.Semantics.Value.sem-case
d_sem'45'case_486 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_sem'45'case_486 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_sem'45'case_486 v5 v6 v7
du_sem'45'case_486 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_sem'45'case_486 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> coe v0 v3
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3 -> coe v1 v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.sem-fst-pair
d_sem'45'fst'45'pair_508 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fst'45'pair_508 = erased
-- Once.Semantics.Value.sem-snd-pair
d_sem'45'snd'45'pair_522 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'snd'45'pair_522 = erased
-- Once.Semantics.Value.sem-case-inl
d_sem'45'case'45'inl_540 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inl_540 = erased
-- Once.Semantics.Value.sem-case-inr
d_sem'45'case'45'inr_560 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inr_560 = erased
-- Once.Semantics.Value.sem-fmap
d_sem'45'fmap_574 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_574 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_sem'45'fmap_574 v2 v5 v6
du_sem'45'fmap_574 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_sem'45'fmap_574 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_112 v3 -> coe v2
      MAlonzo.Code.Once.Type.C_Id_114 -> coe v1 v2
      MAlonzo.Code.Once.Type.C__'8853'__116 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_sem'45'fmap_574 (coe v3) (coe v1) (coe v5))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_sem'45'fmap_574 (coe v4) (coe v1) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__118 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sem'45'fmap_574 (coe v3) (coe v1) (coe v5))
                    (coe du_sem'45'fmap_574 (coe v4) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.sem-fmap-Type
d_sem'45'fmap'45'Type_618 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap'45'Type_618 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_sem'45'fmap'45'Type_618 v2 v5 v6
du_sem'45'fmap'45'Type_618 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_sem'45'fmap'45'Type_618 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_112 v3 -> coe v2
      MAlonzo.Code.Once.Type.C_Id_114 -> coe v1 v2
      MAlonzo.Code.Once.Type.C__'8853'__116 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_sem'45'fmap'45'Type_618 (coe v3) (coe v1) (coe v5))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_sem'45'fmap'45'Type_618 (coe v4) (coe v1) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__118 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sem'45'fmap'45'Type_618 (coe v3) (coe v1) (coe v5))
                    (coe du_sem'45'fmap'45'Type_618 (coe v4) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.fmap-struct-coherence
d_fmap'45'struct'45'coherence_666 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence_666 = erased
-- Once.Semantics.Value.fmap-struct-coherence′
d_fmap'45'struct'45'coherence'8242'_714 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence'8242'_714 = erased
-- Once.Semantics.Value.coerce-full-to-base
d_coerce'45'full'45'to'45'base_754 ::
  () -> () -> MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_754 ~v0 ~v1 v2 v3
  = du_coerce'45'full'45'to'45'base_754 v2 v3
du_coerce'45'full'45'to'45'base_754 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
du_coerce'45'full'45'to'45'base_754 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_120 -> coe v1
      MAlonzo.Code.Once.Type.C_Void_122 -> coe v1
      MAlonzo.Code.Once.Type.C__'42'__124 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coerce'45'full'45'to'45'base_754 (coe v2) (coe v4))
                    (coe du_coerce'45'full'45'to'45'base_754 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'43'__126 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coerce'45'full'45'to'45'base_754 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coerce'45'full'45'to'45'base_754 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v2 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Type.C_μ'45'type_130 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Type.C_ν'45'type_132 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Type.C_Int_134 -> coe v1
      MAlonzo.Code.Once.Type.C_Float_136 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.coerce-base-to-full
d_coerce'45'base'45'to'45'full_786 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_786 ~v0 ~v1 v2 v3 v4
  = du_coerce'45'base'45'to'45'full_786 v2 v3 v4
du_coerce'45'base'45'to'45'full_786 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny -> AgdaAny
du_coerce'45'base'45'to'45'full_786 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_198 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_202 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_204 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_210 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'42'__124 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              du_coerce'45'base'45'to'45'full_786 (coe v7) (coe v5) (coe v9))
                           (coe
                              du_coerce'45'base'45'to'45'full_786 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_216 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__126 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe
                              du_coerce'45'base'45'to'45'full_786 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe
                              du_coerce'45'base'45'to'45'full_786 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.coerce-base-type-round-trip
d_coerce'45'base'45'type'45'round'45'trip_820 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'45'round'45'trip_820 = erased
-- Once.Semantics.Value.coerce-base-type⁻¹-round-trip
d_coerce'45'base'45'type'8315''185''45'round'45'trip_854 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_196 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'8315''185''45'round'45'trip_854 = erased
-- Once.Semantics.Value.coerce-μ-in
d_coerce'45'μ'45'in_886 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_886 ~v0 ~v1 v2 ~v3 v4
  = du_coerce'45'μ'45'in_886 v2 v4
du_coerce'45'μ'45'in_886 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> AgdaAny -> AgdaAny
du_coerce'45'μ'45'in_886 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_112 v2
        -> coe du_coerce'45'full'45'to'45'base_754 (coe v2) (coe v1)
      MAlonzo.Code.Once.Type.C_Id_114 -> coe v1
      MAlonzo.Code.Once.Type.C__'8853'__116 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coerce'45'μ'45'in_886 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coerce'45'μ'45'in_886 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__118 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coerce'45'μ'45'in_886 (coe v2) (coe v4))
                    (coe du_coerce'45'μ'45'in_886 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.coerce-μ-out
d_coerce'45'μ'45'out_928 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_928 ~v0 ~v1 v2 v3 ~v4 v5
  = du_coerce'45'μ'45'out_928 v2 v3 v5
du_coerce'45'μ'45'out_928 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> AgdaAny
du_coerce'45'μ'45'out_928 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_240 v4
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_K_112 v5
               -> coe
                    du_coerce'45'base'45'to'45'full_786 (coe v5) (coe v4) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_242 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_248 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__116 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe du_coerce'45'μ'45'out_928 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe du_coerce'45'μ'45'out_928 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_254 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__118 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe du_coerce'45'μ'45'out_928 (coe v7) (coe v5) (coe v9))
                           (coe du_coerce'45'μ'45'out_928 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.coerce-μ-round-trip
d_coerce'45'μ'45'round'45'trip_974 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'45'round'45'trip_974 = erased
-- Once.Semantics.Value.coerce-μ⁻¹-round-trip
d_coerce'45'μ'8315''185''45'round'45'trip_1020 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'8315''185''45'round'45'trip_1020 = erased
-- Once.Semantics.Value.sem-In
d_sem'45'In_1060 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_μS_182
d_sem'45'In_1060 ~v0 ~v1 v2 v3 = du_sem'45'In_1060 v2 v3
du_sem'45'In_1060 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_μS_182
du_sem'45'In_1060 v0 v1
  = coe
      MAlonzo.Code.Once.Semantics.Functor.C_'10216'_'10217'_186
      (coe du_coerce'45'μ'45'in_886 (coe v0) (coe v1))
-- Once.Semantics.Value.sem-Out
d_sem'45'Out_1068 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'Out_1068 ~v0 ~v1 v2 v3 v4 = du_sem'45'Out_1068 v2 v3 v4
du_sem'45'Out_1068 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
du_sem'45'Out_1068 v0 v1 v2
  = coe
      du_coerce'45'μ'45'out_928 (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.Semantics.Functor.d_outS_190 (coe v2))
-- Once.Semantics.Value.sem-cata
d_sem'45'cata_1080 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'cata_1080 ~v0 ~v1 v2 v3 ~v4 v5
  = du_sem'45'cata_1080 v2 v3 v5
du_sem'45'cata_1080 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
du_sem'45'cata_1080 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Functor.du_cataS_212
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_56 (coe v0))
      (coe
         (\ v3 ->
            coe v2 (coe du_coerce'45'μ'45'out_928 (coe v0) (coe v1) (coe v3))))
-- Once.Semantics.Value.sem-para
d_sem'45'para_1096 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'para_1096 ~v0 ~v1 v2 v3 ~v4 v5 v6
  = du_sem'45'para_1096 v2 v3 v5 v6
du_sem'45'para_1096 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
du_sem'45'para_1096 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         du_sem'45'cata_1080 v0 v1 (coe du_alg''_1112 (coe v0) (coe v2)) v3)
-- Once.Semantics.Value._.alg'
d_alg''_1112 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_alg''_1112 ~v0 ~v1 v2 ~v3 ~v4 v5 ~v6 v7 = du_alg''_1112 v2 v5 v7
du_alg''_1112 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_alg''_1112 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_sem'45'In_1060 (coe v0)
         (coe
            du_sem'45'fmap_574 (coe v0)
            (coe (\ v3 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
            (coe v2)))
      (coe v1 v2)
-- Once.Semantics.Value.coerce-ν-in
d_coerce'45'ν'45'in_1120 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_1120 ~v0 ~v1 = du_coerce'45'ν'45'in_1120
du_coerce'45'ν'45'in_1120 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> () -> AgdaAny -> AgdaAny
du_coerce'45'ν'45'in_1120 v0 v1 v2
  = coe du_coerce'45'μ'45'in_886 v0 v2
-- Once.Semantics.Value.coerce-ν-out
d_coerce'45'ν'45'out_1126 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_1126 ~v0 ~v1 v2
  = du_coerce'45'ν'45'out_1126 v2
du_coerce'45'ν'45'out_1126 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () -> AgdaAny -> AgdaAny
du_coerce'45'ν'45'out_1126 v0 v1 v2 v3
  = coe du_coerce'45'μ'45'out_928 (coe v0) v1 v3
-- Once.Semantics.Value.sem-CoOut
d_sem'45'CoOut_1130 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 ->
  MAlonzo.Code.Once.Res.T_Res_6
d_sem'45'CoOut_1130 ~v0 ~v1 v2 v3 v4
  = du_sem'45'CoOut_1130 v2 v3 v4
du_sem'45'CoOut_1130 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 ->
  MAlonzo.Code.Once.Res.T_Res_6
du_sem'45'CoOut_1130 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Res.du_mapRes_46
      (coe du_coerce'45'ν'45'out_1126 v0 v1 erased)
      (coe MAlonzo.Code.Once.Semantics.Functor.d_unfoldS_204 (coe v2))
-- Once.Semantics.Value.sem-CoIn
d_sem'45'CoIn_1140 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_sem'45'CoIn_1140 ~v0 ~v1 v2 v3 = du_sem'45'CoIn_1140 v2 v3
du_sem'45'CoIn_1140 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
du_sem'45'CoIn_1140 v0 v1
  = coe
      MAlonzo.Code.Once.Semantics.Functor.C_constructor_206
      (coe
         MAlonzo.Code.Once.Res.C_returns_12
         (coe du_coerce'45'ν'45'in_1120 v0 erased v1))
-- Once.Semantics.Value.sem-CoOut-CoIn
d_sem'45'CoOut'45'CoIn_1152 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoOut'45'CoIn_1152 = erased
-- Once.Semantics.Value.sem-ana
d_sem'45'ana_1164 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_sem'45'ana_1164 ~v0 ~v1 v2 ~v3 v4 v5
  = du_sem'45'ana_1164 v2 v4 v5
du_sem'45'ana_1164 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
du_sem'45'ana_1164 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Functor.C_constructor_206
      (coe du_semAnaLayer_1170 (coe v0) (coe v1) (coe v1 v2))
-- Once.Semantics.Value.semAnaLayer
d_semAnaLayer_1170 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Res.T_Res_6 -> MAlonzo.Code.Once.Res.T_Res_6
d_semAnaLayer_1170 ~v0 ~v1 v2 ~v3 v4 v5
  = du_semAnaLayer_1170 v2 v4 v5
du_semAnaLayer_1170 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Res.T_Res_6 -> MAlonzo.Code.Once.Res.T_Res_6
du_semAnaLayer_1170 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Res.C_stopped_10 -> coe v2
      MAlonzo.Code.Once.Res.C_returns_12 v3
        -> coe
             MAlonzo.Code.Once.Res.C_returns_12
             (coe
                du_sfmapSemAna_1178 (coe v0)
                (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_56 (coe v0))
                (coe v1) (coe du_coerce'45'ν'45'in_1120 v0 erased v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.sfmapSemAna
d_sfmapSemAna_1178 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) -> AgdaAny -> AgdaAny
d_sfmapSemAna_1178 ~v0 ~v1 v2 v3 ~v4 v5 v6
  = du_sfmapSemAna_1178 v2 v3 v5 v6
du_sfmapSemAna_1178 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) -> AgdaAny -> AgdaAny
du_sfmapSemAna_1178 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Semantics.Functor.C_SK_8 -> coe v3
      MAlonzo.Code.Once.Semantics.Functor.C_SId_10
        -> coe du_sem'45'ana_1164 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.Semantics.Functor.C__S'8853'__12 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_sfmapSemAna_1178 (coe v0) (coe v4) (coe v2) (coe v6))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_sfmapSemAna_1178 (coe v0) (coe v5) (coe v2) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Semantics.Functor.C__S'8855'__14 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sfmapSemAna_1178 (coe v0) (coe v4) (coe v2) (coe v6))
                    (coe du_sfmapSemAna_1178 (coe v0) (coe v5) (coe v2) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.sfmapSemAna-is-sfmap
d_sfmapSemAna'45'is'45'sfmap_1258 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmapSemAna'45'is'45'sfmap_1258 = erased
-- Once.Semantics.Value.sem-fuseNat
d_sem'45'fuseNat_1314 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'fuseNat_1314 ~v0 ~v1 v2 v3 v4 v5 ~v6 v7 v8
  = du_sem'45'fuseNat_1314 v2 v3 v4 v5 v7 v8
du_sem'45'fuseNat_1314 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
du_sem'45'fuseNat_1314 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Semantics.Functor.du_fuseNatS_668
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_56 (coe v1))
      erased
      (coe
         (\ v6 v7 ->
            coe
              du_coerce'45'μ'45'in_886 (coe v0)
              (coe
                 v4 v6 (coe du_coerce'45'μ'45'out_928 (coe v1) (coe v3) (coe v7)))))
      (coe
         (\ v6 ->
            coe v5 (coe du_coerce'45'μ'45'out_928 (coe v0) (coe v2) (coe v6))))
-- Once.Semantics.Value.sem-fuseNat-cong
d_sem'45'fuseNat'45'cong_1358 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (() ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fuseNat'45'cong_1358 = erased
-- Once.Semantics.Value._.Φ-eq
d_Φ'45'eq_1390 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (() ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_Φ'45'eq_1390 = erased
-- Once.Semantics.Value.sem-fuseNat-events
d_sem'45'fuseNat'45'events_1410 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'fuseNat'45'events_1410 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 ~v9
                                v10 v11
  = du_sem'45'fuseNat'45'events_1410 v3 v4 v5 v6 v7 v8 v10 v11
du_sem'45'fuseNat'45'events_1410 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sem'45'fuseNat'45'events_1410 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Semantics.Functor.du_fuseNatW_690
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_56 (coe v2))
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_56 (coe v3))
      (coe v0) (coe v1)
      (coe
         (\ v8 v9 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
              (coe
                 du_coerce'45'μ'45'in_886 (coe v2)
                 (coe
                    v6 v8
                    (coe du_coerce'45'μ'45'out_928 (coe v3) (coe v5) (coe v9))))))
      (coe
         (\ v8 ->
            coe v7 (coe du_coerce'45'μ'45'out_928 (coe v2) (coe v4) (coe v8))))
-- Once.Semantics.Value.sem-Out-In
d_sem'45'Out'45'In_1444 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'Out'45'In_1444 = erased
-- Once.Semantics.Value.sem-In-Out
d_sem'45'In'45'Out_1456 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'In'45'Out_1456 = erased
-- Once.Semantics.Value.fmap-coerce-μ-coherence
d_fmap'45'coerce'45'μ'45'coherence_1472 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence_1472 = erased
-- Once.Semantics.Value.fmap-coerce-μ-coherence′
d_fmap'45'coerce'45'μ'45'coherence'8242'_1522 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence'8242'_1522 = erased
-- Once.Semantics.Value.sem-cata-compute
d_sem'45'cata'45'compute_1570 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'compute_1570 = erased
