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
-- Once.Semantics.Value.⟦_⟧F
d_'10214'_'10215'F_46 ::
  () -> () -> MAlonzo.Code.Once.Type.T_Functor_106 -> () -> ()
d_'10214'_'10215'F_46 = erased
-- Once.Semantics.Value.sem-functor-coherence
d_sem'45'functor'45'coherence_70 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'functor'45'coherence_70 = erased
-- Once.Semantics.Value.coerce-functor
d_coerce'45'functor_110 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'functor_110 ~v0 ~v1 v2 ~v3 v4
  = du_coerce'45'functor_110 v2 v4
du_coerce'45'functor_110 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> AgdaAny -> AgdaAny
du_coerce'45'functor_110 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_110 v2 -> coe v1
      MAlonzo.Code.Once.Type.C_Id_112 -> coe v1
      MAlonzo.Code.Once.Type.C__'8853'__114 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coerce'45'functor_110 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coerce'45'functor_110 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__116 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coerce'45'functor_110 (coe v2) (coe v4))
                    (coe du_coerce'45'functor_110 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_152 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_152 ~v0 ~v1 v2 ~v3 v4
  = du_coerce'45'functor'8315''185'_152 v2 v4
du_coerce'45'functor'8315''185'_152 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> AgdaAny -> AgdaAny
du_coerce'45'functor'8315''185'_152 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_110 v2 -> coe v1
      MAlonzo.Code.Once.Type.C_Id_112 -> coe v1
      MAlonzo.Code.Once.Type.C__'8853'__114 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coerce'45'functor'8315''185'_152 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coerce'45'functor'8315''185'_152 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__116 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coerce'45'functor'8315''185'_152 (coe v2) (coe v4))
                    (coe du_coerce'45'functor'8315''185'_152 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.coerce-round-trip
d_coerce'45'round'45'trip_196 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'round'45'trip_196 = erased
-- Once.Semantics.Value.coerce⁻¹-round-trip
d_coerce'8315''185''45'round'45'trip_240 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'8315''185''45'round'45'trip_240 = erased
-- Once.Semantics.Value.coerce-struct
d_coerce'45'struct_282 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'struct_282 ~v0 ~v1 = du_coerce'45'struct_282
du_coerce'45'struct_282 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
du_coerce'45'struct_282 v0 v1 v2
  = coe du_coerce'45'functor_110 v0 v2
-- Once.Semantics.Value.coerce-struct⁻¹
d_coerce'45'struct'8315''185'_288 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'struct'8315''185'_288 ~v0 ~v1
  = du_coerce'45'struct'8315''185'_288
du_coerce'45'struct'8315''185'_288 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
du_coerce'45'struct'8315''185'_288 v0 v1 v2
  = coe du_coerce'45'functor'8315''185'_152 v0 v2
-- Once.Semantics.Value.coerce-struct-round-trip
d_coerce'45'struct'45'round'45'trip_296 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'45'round'45'trip_296 = erased
-- Once.Semantics.Value.coerce-struct⁻¹-round-trip
d_coerce'45'struct'8315''185''45'round'45'trip_304 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'8315''185''45'round'45'trip_304 = erased
-- Once.Semantics.Value.sem-fst
d_sem'45'fst_310 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'fst_310 ~v0 ~v1 ~v2 ~v3 v4 = du_sem'45'fst_310 v4
du_sem'45'fst_310 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_sem'45'fst_310 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)
-- Once.Semantics.Value.sem-snd
d_sem'45'snd_316 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'snd_316 ~v0 ~v1 ~v2 ~v3 v4 = du_sem'45'snd_316 v4
du_sem'45'snd_316 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_sem'45'snd_316 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)
-- Once.Semantics.Value.sem-pair
d_sem'45'pair_322 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'pair_322 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_sem'45'pair_322 v4 v5
du_sem'45'pair_322 ::
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sem'45'pair_322 v0 v1
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
-- Once.Semantics.Value.sem-inl
d_sem'45'inl_332 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inl_332 ~v0 ~v1 ~v2 ~v3 = du_sem'45'inl_332
du_sem'45'inl_332 ::
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sem'45'inl_332 = coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
-- Once.Semantics.Value.sem-inr
d_sem'45'inr_338 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inr_338 ~v0 ~v1 ~v2 ~v3 = du_sem'45'inr_338
du_sem'45'inr_338 ::
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sem'45'inr_338 = coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
-- Once.Semantics.Value.sem-case
d_sem'45'case_346 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_sem'45'case_346 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_sem'45'case_346 v5 v6 v7
du_sem'45'case_346 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_sem'45'case_346 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> coe v0 v3
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3 -> coe v1 v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.sem-fst-pair
d_sem'45'fst'45'pair_368 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fst'45'pair_368 = erased
-- Once.Semantics.Value.sem-snd-pair
d_sem'45'snd'45'pair_382 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'snd'45'pair_382 = erased
-- Once.Semantics.Value.sem-case-inl
d_sem'45'case'45'inl_400 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inl_400 = erased
-- Once.Semantics.Value.sem-case-inr
d_sem'45'case'45'inr_420 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inr_420 = erased
-- Once.Semantics.Value.sem-fmap
d_sem'45'fmap_434 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_434 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_sem'45'fmap_434 v2 v5 v6
du_sem'45'fmap_434 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_sem'45'fmap_434 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_110 v3 -> coe v2
      MAlonzo.Code.Once.Type.C_Id_112 -> coe v1 v2
      MAlonzo.Code.Once.Type.C__'8853'__114 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_sem'45'fmap_434 (coe v3) (coe v1) (coe v5))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_sem'45'fmap_434 (coe v4) (coe v1) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__116 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sem'45'fmap_434 (coe v3) (coe v1) (coe v5))
                    (coe du_sem'45'fmap_434 (coe v4) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.sem-fmap-Type
d_sem'45'fmap'45'Type_478 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap'45'Type_478 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_sem'45'fmap'45'Type_478 v2 v5 v6
du_sem'45'fmap'45'Type_478 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_sem'45'fmap'45'Type_478 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_110 v3 -> coe v2
      MAlonzo.Code.Once.Type.C_Id_112 -> coe v1 v2
      MAlonzo.Code.Once.Type.C__'8853'__114 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_sem'45'fmap'45'Type_478 (coe v3) (coe v1) (coe v5))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_sem'45'fmap'45'Type_478 (coe v4) (coe v1) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__116 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sem'45'fmap'45'Type_478 (coe v3) (coe v1) (coe v5))
                    (coe du_sem'45'fmap'45'Type_478 (coe v4) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.fmap-struct-coherence
d_fmap'45'struct'45'coherence_526 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence_526 = erased
-- Once.Semantics.Value.fmap-struct-coherence′
d_fmap'45'struct'45'coherence'8242'_574 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence'8242'_574 = erased
-- Once.Semantics.Value.coerce-full-to-base
d_coerce'45'full'45'to'45'base_614 ::
  () -> () -> MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_614 ~v0 ~v1 v2 v3
  = du_coerce'45'full'45'to'45'base_614 v2 v3
du_coerce'45'full'45'to'45'base_614 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
du_coerce'45'full'45'to'45'base_614 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_118 -> coe v1
      MAlonzo.Code.Once.Type.C_Void_120 -> coe v1
      MAlonzo.Code.Once.Type.C__'42'__122 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coerce'45'full'45'to'45'base_614 (coe v2) (coe v4))
                    (coe du_coerce'45'full'45'to'45'base_614 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'43'__124 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coerce'45'full'45'to'45'base_614 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coerce'45'full'45'to'45'base_614 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v2 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Type.C_μ'45'type_128 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Type.C_ν'45'type_130 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Type.C_Int_132 -> coe v1
      MAlonzo.Code.Once.Type.C_Float_134 -> coe v1
      MAlonzo.Code.Once.Type.C_Str_136 -> coe v1
      MAlonzo.Code.Once.Type.C_Buffer_138 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.coerce-base-to-full
d_coerce'45'base'45'to'45'full_650 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_650 ~v0 ~v1 v2 v3 v4
  = du_coerce'45'base'45'to'45'full_650 v2 v3 v4
du_coerce'45'base'45'to'45'full_650 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> AgdaAny
du_coerce'45'base'45'to'45'full_650 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_206 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_208 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Str_210 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Buffer_212 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_218 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'42'__122 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              du_coerce'45'base'45'to'45'full_650 (coe v7) (coe v5) (coe v9))
                           (coe
                              du_coerce'45'base'45'to'45'full_650 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_224 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__124 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe
                              du_coerce'45'base'45'to'45'full_650 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe
                              du_coerce'45'base'45'to'45'full_650 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.coerce-base-type-round-trip
d_coerce'45'base'45'type'45'round'45'trip_688 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'45'round'45'trip_688 = erased
-- Once.Semantics.Value.coerce-base-type⁻¹-round-trip
d_coerce'45'base'45'type'8315''185''45'round'45'trip_726 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'8315''185''45'round'45'trip_726 = erased
-- Once.Semantics.Value.coerce-μ-in
d_coerce'45'μ'45'in_762 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_762 ~v0 ~v1 v2 ~v3 v4
  = du_coerce'45'μ'45'in_762 v2 v4
du_coerce'45'μ'45'in_762 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> AgdaAny -> AgdaAny
du_coerce'45'μ'45'in_762 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_110 v2
        -> coe du_coerce'45'full'45'to'45'base_614 (coe v2) (coe v1)
      MAlonzo.Code.Once.Type.C_Id_112 -> coe v1
      MAlonzo.Code.Once.Type.C__'8853'__114 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coerce'45'μ'45'in_762 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coerce'45'μ'45'in_762 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__116 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coerce'45'μ'45'in_762 (coe v2) (coe v4))
                    (coe du_coerce'45'μ'45'in_762 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.coerce-μ-out
d_coerce'45'μ'45'out_804 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_804 ~v0 ~v1 v2 v3 ~v4 v5
  = du_coerce'45'μ'45'out_804 v2 v3 v5
du_coerce'45'μ'45'out_804 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny -> AgdaAny
du_coerce'45'μ'45'out_804 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_244 v4
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_K_110 v5
               -> coe
                    du_coerce'45'base'45'to'45'full_650 (coe v5) (coe v4) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_246 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_252 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__114 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe du_coerce'45'μ'45'out_804 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe du_coerce'45'μ'45'out_804 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_258 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__116 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe du_coerce'45'μ'45'out_804 (coe v7) (coe v5) (coe v9))
                           (coe du_coerce'45'μ'45'out_804 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.coerce-μ-round-trip
d_coerce'45'μ'45'round'45'trip_850 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'45'round'45'trip_850 = erased
-- Once.Semantics.Value.coerce-μ⁻¹-round-trip
d_coerce'45'μ'8315''185''45'round'45'trip_896 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'8315''185''45'round'45'trip_896 = erased
-- Once.Semantics.Value.sem-In
d_sem'45'In_936 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_μS_182
d_sem'45'In_936 ~v0 ~v1 v2 v3 = du_sem'45'In_936 v2 v3
du_sem'45'In_936 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_μS_182
du_sem'45'In_936 v0 v1
  = coe
      MAlonzo.Code.Once.Semantics.Functor.C_'10216'_'10217'_186
      (coe du_coerce'45'μ'45'in_762 (coe v0) (coe v1))
-- Once.Semantics.Value.sem-Out
d_sem'45'Out_944 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'Out_944 ~v0 ~v1 v2 v3 v4 = du_sem'45'Out_944 v2 v3 v4
du_sem'45'Out_944 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
du_sem'45'Out_944 v0 v1 v2
  = coe
      du_coerce'45'μ'45'out_804 (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.Semantics.Functor.d_outS_190 (coe v2))
-- Once.Semantics.Value.sem-cata
d_sem'45'cata_956 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'cata_956 ~v0 ~v1 v2 v3 ~v4 v5
  = du_sem'45'cata_956 v2 v3 v5
du_sem'45'cata_956 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
du_sem'45'cata_956 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Functor.du_cataS_212
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_60 (coe v0))
      (coe
         (\ v3 ->
            coe v2 (coe du_coerce'45'μ'45'out_804 (coe v0) (coe v1) (coe v3))))
-- Once.Semantics.Value.sem-para
d_sem'45'para_972 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'para_972 ~v0 ~v1 v2 v3 ~v4 v5 v6
  = du_sem'45'para_972 v2 v3 v5 v6
du_sem'45'para_972 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
du_sem'45'para_972 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         du_sem'45'cata_956 v0 v1 (coe du_alg''_988 (coe v0) (coe v2)) v3)
-- Once.Semantics.Value._.alg'
d_alg''_988 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_alg''_988 ~v0 ~v1 v2 ~v3 ~v4 v5 ~v6 v7 = du_alg''_988 v2 v5 v7
du_alg''_988 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_alg''_988 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_sem'45'In_936 (coe v0)
         (coe
            du_sem'45'fmap_434 (coe v0)
            (coe (\ v3 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
            (coe v2)))
      (coe v1 v2)
-- Once.Semantics.Value.coerce-ν-in
d_coerce'45'ν'45'in_996 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_996 ~v0 ~v1 = du_coerce'45'ν'45'in_996
du_coerce'45'ν'45'in_996 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> () -> AgdaAny -> AgdaAny
du_coerce'45'ν'45'in_996 v0 v1 v2
  = coe du_coerce'45'μ'45'in_762 v0 v2
-- Once.Semantics.Value.coerce-ν-out
d_coerce'45'ν'45'out_1002 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_1002 ~v0 ~v1 v2
  = du_coerce'45'ν'45'out_1002 v2
du_coerce'45'ν'45'out_1002 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () -> AgdaAny -> AgdaAny
du_coerce'45'ν'45'out_1002 v0 v1 v2 v3
  = coe du_coerce'45'μ'45'out_804 (coe v0) v1 v3
-- Once.Semantics.Value.sem-CoOut
d_sem'45'CoOut_1006 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 -> AgdaAny
d_sem'45'CoOut_1006 ~v0 ~v1 v2 v3 v4
  = du_sem'45'CoOut_1006 v2 v3 v4
du_sem'45'CoOut_1006 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 -> AgdaAny
du_sem'45'CoOut_1006 v0 v1 v2
  = coe
      du_coerce'45'ν'45'out_1002 v0 v1 erased
      (MAlonzo.Code.Once.Semantics.Functor.d_unfoldS_204 (coe v2))
-- Once.Semantics.Value.sem-CoIn
d_sem'45'CoIn_1016 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_sem'45'CoIn_1016 ~v0 ~v1 v2 v3 = du_sem'45'CoIn_1016 v2 v3
du_sem'45'CoIn_1016 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
du_sem'45'CoIn_1016 v0 v1
  = coe
      MAlonzo.Code.Once.Semantics.Functor.C_constructor_206
      (coe du_coerce'45'ν'45'in_996 v0 erased v1)
-- Once.Semantics.Value.sem-CoOut-CoIn
d_sem'45'CoOut'45'CoIn_1028 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoOut'45'CoIn_1028 = erased
-- Once.Semantics.Value.sem-ana
d_sem'45'ana_1040 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_sem'45'ana_1040 ~v0 ~v1 v2 ~v3 v4 v5
  = du_sem'45'ana_1040 v2 v4 v5
du_sem'45'ana_1040 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
du_sem'45'ana_1040 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Functor.C_constructor_206
      (coe
         du_sfmapSemAna_1048 (coe v0)
         (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_60 (coe v0))
         (coe v1) (coe du_coerce'45'ν'45'in_996 v0 erased (coe v1 v2)))
-- Once.Semantics.Value.sfmapSemAna
d_sfmapSemAna_1048 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sfmapSemAna_1048 ~v0 ~v1 v2 v3 ~v4 v5 v6
  = du_sfmapSemAna_1048 v2 v3 v5 v6
du_sfmapSemAna_1048 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_sfmapSemAna_1048 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Semantics.Functor.C_SK_8 -> coe v3
      MAlonzo.Code.Once.Semantics.Functor.C_SId_10
        -> coe du_sem'45'ana_1040 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.Semantics.Functor.C__S'8853'__12 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_sfmapSemAna_1048 (coe v0) (coe v4) (coe v2) (coe v6))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_sfmapSemAna_1048 (coe v0) (coe v5) (coe v2) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Semantics.Functor.C__S'8855'__14 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sfmapSemAna_1048 (coe v0) (coe v4) (coe v2) (coe v6))
                    (coe du_sfmapSemAna_1048 (coe v0) (coe v5) (coe v2) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.sfmapSemAna-is-sfmap
d_sfmapSemAna'45'is'45'sfmap_1114 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmapSemAna'45'is'45'sfmap_1114 = erased
-- Once.Semantics.Value.sem-fuseNat
d_sem'45'fuseNat_1170 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'fuseNat_1170 ~v0 ~v1 v2 v3 v4 v5 ~v6 v7 v8
  = du_sem'45'fuseNat_1170 v2 v3 v4 v5 v7 v8
du_sem'45'fuseNat_1170 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
du_sem'45'fuseNat_1170 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Semantics.Functor.du_fuseNatS_632
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_60 (coe v1))
      erased
      (coe
         (\ v6 v7 ->
            coe
              du_coerce'45'μ'45'in_762 (coe v0)
              (coe
                 v4 v6 (coe du_coerce'45'μ'45'out_804 (coe v1) (coe v3) (coe v7)))))
      (coe
         (\ v6 ->
            coe v5 (coe du_coerce'45'μ'45'out_804 (coe v0) (coe v2) (coe v6))))
-- Once.Semantics.Value.sem-fuseNat-cong
d_sem'45'fuseNat'45'cong_1214 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
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
d_sem'45'fuseNat'45'cong_1214 = erased
-- Once.Semantics.Value._.Φ-eq
d_Φ'45'eq_1246 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
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
d_Φ'45'eq_1246 = erased
-- Once.Semantics.Value.sem-fuseNat-events
d_sem'45'fuseNat'45'events_1266 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'fuseNat'45'events_1266 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 ~v9
                                v10 v11
  = du_sem'45'fuseNat'45'events_1266 v3 v4 v5 v6 v7 v8 v10 v11
du_sem'45'fuseNat'45'events_1266 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sem'45'fuseNat'45'events_1266 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Semantics.Functor.du_fuseNatW_654
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_60 (coe v2))
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_60 (coe v3))
      (coe v0) (coe v1)
      (coe
         (\ v8 v9 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
              (coe
                 du_coerce'45'μ'45'in_762 (coe v2)
                 (coe
                    v6 v8
                    (coe du_coerce'45'μ'45'out_804 (coe v3) (coe v5) (coe v9))))))
      (coe
         (\ v8 ->
            coe v7 (coe du_coerce'45'μ'45'out_804 (coe v2) (coe v4) (coe v8))))
-- Once.Semantics.Value.sem-Out-In
d_sem'45'Out'45'In_1300 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'Out'45'In_1300 = erased
-- Once.Semantics.Value.sem-In-Out
d_sem'45'In'45'Out_1312 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'In'45'Out_1312 = erased
-- Once.Semantics.Value.fmap-coerce-μ-coherence
d_fmap'45'coerce'45'μ'45'coherence_1328 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence_1328 = erased
-- Once.Semantics.Value.fmap-coerce-μ-coherence′
d_fmap'45'coerce'45'μ'45'coherence'8242'_1378 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence'8242'_1378 = erased
-- Once.Semantics.Value.sem-cata-compute
d_sem'45'cata'45'compute_1426 ::
  () ->
  () ->
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'compute_1426 = erased
