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

module MAlonzo.Code.Once.Semantics.Core where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Functor.Base
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Type

-- Once.Semantics.Core.funext
d_funext_20
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Semantics.Core.funext"
-- Once.Semantics.Core.⟦μ⟧
d_'10214'μ'10215'_22 ::
  () -> MAlonzo.Code.Once.Type.T_Functor_110 -> ()
d_'10214'μ'10215'_22 = erased
-- Once.Semantics.Core.⟦ν⟧
d_'10214'ν'10215'_24 ::
  () -> MAlonzo.Code.Once.Type.T_Functor_110 -> ()
d_'10214'ν'10215'_24 = erased
-- Once.Semantics.Core.⟦_⟧
d_'10214'_'10215'_26 ::
  () -> MAlonzo.Code.Once.Type.T_Type_112 -> ()
d_'10214'_'10215'_26 = erased
-- Once.Semantics.Core.⟦_⟧F
d_'10214'_'10215'F_44 ::
  () -> MAlonzo.Code.Once.Type.T_Functor_110 -> () -> ()
d_'10214'_'10215'F_44 = erased
-- Once.Semantics.Core.sem-functor-coherence
d_sem'45'functor'45'coherence_68 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'functor'45'coherence_68 = erased
-- Once.Semantics.Core.coerce-functor
d_coerce'45'functor_108 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'functor_108 ~v0 v1 ~v2 v3
  = du_coerce'45'functor_108 v1 v3
du_coerce'45'functor_108 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> AgdaAny -> AgdaAny
du_coerce'45'functor_108 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_114 v2 -> coe v1
      MAlonzo.Code.Once.Type.C_Id_116 -> coe v1
      MAlonzo.Code.Once.Type.C__'8853'__118 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coerce'45'functor_108 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coerce'45'functor_108 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__120 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coerce'45'functor_108 (coe v2) (coe v4))
                    (coe du_coerce'45'functor_108 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Core.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_150 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_150 ~v0 v1 ~v2 v3
  = du_coerce'45'functor'8315''185'_150 v1 v3
du_coerce'45'functor'8315''185'_150 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> AgdaAny -> AgdaAny
du_coerce'45'functor'8315''185'_150 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_114 v2 -> coe v1
      MAlonzo.Code.Once.Type.C_Id_116 -> coe v1
      MAlonzo.Code.Once.Type.C__'8853'__118 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coerce'45'functor'8315''185'_150 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coerce'45'functor'8315''185'_150 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__120 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coerce'45'functor'8315''185'_150 (coe v2) (coe v4))
                    (coe du_coerce'45'functor'8315''185'_150 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Core.coerce-round-trip
d_coerce'45'round'45'trip_194 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'round'45'trip_194 = erased
-- Once.Semantics.Core.coerce⁻¹-round-trip
d_coerce'8315''185''45'round'45'trip_238 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'8315''185''45'round'45'trip_238 = erased
-- Once.Semantics.Core.coerce-struct
d_coerce'45'struct_280 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'struct_280 ~v0 = du_coerce'45'struct_280
du_coerce'45'struct_280 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
du_coerce'45'struct_280 v0 v1 v2
  = coe du_coerce'45'functor_108 v0 v2
-- Once.Semantics.Core.coerce-struct⁻¹
d_coerce'45'struct'8315''185'_286 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'struct'8315''185'_286 ~v0
  = du_coerce'45'struct'8315''185'_286
du_coerce'45'struct'8315''185'_286 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
du_coerce'45'struct'8315''185'_286 v0 v1 v2
  = coe du_coerce'45'functor'8315''185'_150 v0 v2
-- Once.Semantics.Core.coerce-struct-round-trip
d_coerce'45'struct'45'round'45'trip_294 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'45'round'45'trip_294 = erased
-- Once.Semantics.Core.coerce-struct⁻¹-round-trip
d_coerce'45'struct'8315''185''45'round'45'trip_302 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'8315''185''45'round'45'trip_302 = erased
-- Once.Semantics.Core.sem-fst
d_sem'45'fst_308 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'fst_308 ~v0 ~v1 ~v2 v3 = du_sem'45'fst_308 v3
du_sem'45'fst_308 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_sem'45'fst_308 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)
-- Once.Semantics.Core.sem-snd
d_sem'45'snd_314 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'snd_314 ~v0 ~v1 ~v2 v3 = du_sem'45'snd_314 v3
du_sem'45'snd_314 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_sem'45'snd_314 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)
-- Once.Semantics.Core.sem-pair
d_sem'45'pair_320 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'pair_320 ~v0 ~v1 ~v2 v3 v4 = du_sem'45'pair_320 v3 v4
du_sem'45'pair_320 ::
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sem'45'pair_320 v0 v1
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
-- Once.Semantics.Core.sem-inl
d_sem'45'inl_330 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inl_330 ~v0 ~v1 ~v2 = du_sem'45'inl_330
du_sem'45'inl_330 ::
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sem'45'inl_330 = coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
-- Once.Semantics.Core.sem-inr
d_sem'45'inr_336 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inr_336 ~v0 ~v1 ~v2 = du_sem'45'inr_336
du_sem'45'inr_336 ::
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sem'45'inr_336 = coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
-- Once.Semantics.Core.sem-case
d_sem'45'case_344 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_sem'45'case_344 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_sem'45'case_344 v4 v5 v6
du_sem'45'case_344 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_sem'45'case_344 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> coe v0 v3
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3 -> coe v1 v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Core.sem-fst-pair
d_sem'45'fst'45'pair_366 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fst'45'pair_366 = erased
-- Once.Semantics.Core.sem-snd-pair
d_sem'45'snd'45'pair_380 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'snd'45'pair_380 = erased
-- Once.Semantics.Core.sem-case-inl
d_sem'45'case'45'inl_398 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inl_398 = erased
-- Once.Semantics.Core.sem-case-inr
d_sem'45'case'45'inr_418 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inr_418 = erased
-- Once.Semantics.Core.sem-fmap
d_sem'45'fmap_432 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_432 ~v0 v1 ~v2 ~v3 v4 v5
  = du_sem'45'fmap_432 v1 v4 v5
du_sem'45'fmap_432 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_sem'45'fmap_432 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_114 v3 -> coe v2
      MAlonzo.Code.Once.Type.C_Id_116 -> coe v1 v2
      MAlonzo.Code.Once.Type.C__'8853'__118 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_sem'45'fmap_432 (coe v3) (coe v1) (coe v5))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_sem'45'fmap_432 (coe v4) (coe v1) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__120 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sem'45'fmap_432 (coe v3) (coe v1) (coe v5))
                    (coe du_sem'45'fmap_432 (coe v4) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Core.sem-fmap-Type
d_sem'45'fmap'45'Type_476 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap'45'Type_476 ~v0 v1 ~v2 ~v3 v4 v5
  = du_sem'45'fmap'45'Type_476 v1 v4 v5
du_sem'45'fmap'45'Type_476 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_sem'45'fmap'45'Type_476 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_114 v3 -> coe v2
      MAlonzo.Code.Once.Type.C_Id_116 -> coe v1 v2
      MAlonzo.Code.Once.Type.C__'8853'__118 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_sem'45'fmap'45'Type_476 (coe v3) (coe v1) (coe v5))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_sem'45'fmap'45'Type_476 (coe v4) (coe v1) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__120 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sem'45'fmap'45'Type_476 (coe v3) (coe v1) (coe v5))
                    (coe du_sem'45'fmap'45'Type_476 (coe v4) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Core.fmap-struct-coherence
d_fmap'45'struct'45'coherence_524 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence_524 = erased
-- Once.Semantics.Core.fmap-struct-coherence′
d_fmap'45'struct'45'coherence'8242'_572 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence'8242'_572 = erased
-- Once.Semantics.Core.coerce-full-to-base
d_coerce'45'full'45'to'45'base_612 ::
  () -> MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_612 ~v0 v1 v2
  = du_coerce'45'full'45'to'45'base_612 v1 v2
du_coerce'45'full'45'to'45'base_612 ::
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
du_coerce'45'full'45'to'45'base_612 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_122 -> coe v1
      MAlonzo.Code.Once.Type.C_Void_124 -> coe v1
      MAlonzo.Code.Once.Type.C__'42'__126 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coerce'45'full'45'to'45'base_612 (coe v2) (coe v4))
                    (coe du_coerce'45'full'45'to'45'base_612 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'43'__128 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coerce'45'full'45'to'45'base_612 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coerce'45'full'45'to'45'base_612 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v2 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Type.C_μ'45'type_132 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Type.C_ν'45'type_134 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Type.C_Int_136 -> coe v1
      MAlonzo.Code.Once.Type.C_Float_138 -> coe v1
      MAlonzo.Code.Once.Type.C_Str_140 -> coe v1
      MAlonzo.Code.Once.Type.C_Buffer_142 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Core.coerce-base-to-full
d_coerce'45'base'45'to'45'full_648 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_648 ~v0 v1 v2 v3
  = du_coerce'45'base'45'to'45'full_648 v1 v2 v3
du_coerce'45'base'45'to'45'full_648 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> AgdaAny
du_coerce'45'base'45'to'45'full_648 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_150 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_154 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_156 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Str_158 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Buffer_160 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_166 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'42'__126 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              du_coerce'45'base'45'to'45'full_648 (coe v7) (coe v5) (coe v9))
                           (coe
                              du_coerce'45'base'45'to'45'full_648 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_172 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__128 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe
                              du_coerce'45'base'45'to'45'full_648 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe
                              du_coerce'45'base'45'to'45'full_648 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Core.coerce-base-type-round-trip
d_coerce'45'base'45'type'45'round'45'trip_686 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'45'round'45'trip_686 = erased
-- Once.Semantics.Core.coerce-base-type⁻¹-round-trip
d_coerce'45'base'45'type'8315''185''45'round'45'trip_724 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'8315''185''45'round'45'trip_724 = erased
-- Once.Semantics.Core.coerce-μ-in
d_coerce'45'μ'45'in_760 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_760 ~v0 v1 ~v2 v3
  = du_coerce'45'μ'45'in_760 v1 v3
du_coerce'45'μ'45'in_760 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> AgdaAny -> AgdaAny
du_coerce'45'μ'45'in_760 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_114 v2
        -> coe du_coerce'45'full'45'to'45'base_612 (coe v2) (coe v1)
      MAlonzo.Code.Once.Type.C_Id_116 -> coe v1
      MAlonzo.Code.Once.Type.C__'8853'__118 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coerce'45'μ'45'in_760 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coerce'45'μ'45'in_760 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__120 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coerce'45'μ'45'in_760 (coe v2) (coe v4))
                    (coe du_coerce'45'μ'45'in_760 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Core.coerce-μ-out
d_coerce'45'μ'45'out_802 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_802 ~v0 v1 v2 ~v3 v4
  = du_coerce'45'μ'45'out_802 v1 v2 v4
du_coerce'45'μ'45'out_802 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny -> AgdaAny
du_coerce'45'μ'45'out_802 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_178 v4
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_K_114 v5
               -> coe
                    du_coerce'45'base'45'to'45'full_648 (coe v5) (coe v4) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_180 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_186 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe du_coerce'45'μ'45'out_802 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe du_coerce'45'μ'45'out_802 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_192 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe du_coerce'45'μ'45'out_802 (coe v7) (coe v5) (coe v9))
                           (coe du_coerce'45'μ'45'out_802 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Core.coerce-μ-round-trip
d_coerce'45'μ'45'round'45'trip_848 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'45'round'45'trip_848 = erased
-- Once.Semantics.Core.coerce-μ⁻¹-round-trip
d_coerce'45'μ'8315''185''45'round'45'trip_894 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'8315''185''45'round'45'trip_894 = erased
-- Once.Semantics.Core.sem-In
d_sem'45'In_934 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_μS_230
d_sem'45'In_934 ~v0 v1 v2 = du_sem'45'In_934 v1 v2
du_sem'45'In_934 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_μS_230
du_sem'45'In_934 v0 v1
  = coe
      MAlonzo.Code.Once.Functor.Base.C_'10216'_'10217'_234
      (coe du_coerce'45'μ'45'in_760 (coe v0) (coe v1))
-- Once.Semantics.Core.sem-Out
d_sem'45'Out_942 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'Out_942 ~v0 v1 v2 v3 = du_sem'45'Out_942 v1 v2 v3
du_sem'45'Out_942 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
du_sem'45'Out_942 v0 v1 v2
  = coe
      du_coerce'45'μ'45'out_802 (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.Functor.Base.d_outS_238 (coe v2))
-- Once.Semantics.Core.sem-cata
d_sem'45'cata_954 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'cata_954 ~v0 v1 v2 ~v3 v4 = du_sem'45'cata_954 v1 v2 v4
du_sem'45'cata_954 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
du_sem'45'cata_954 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Functor.Base.du_cataS_260
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_38 (coe v0))
      (coe
         (\ v3 ->
            coe v2 (coe du_coerce'45'μ'45'out_802 (coe v0) (coe v1) (coe v3))))
-- Once.Semantics.Core.sem-para
d_sem'45'para_970 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'para_970 ~v0 v1 v2 ~v3 v4 v5
  = du_sem'45'para_970 v1 v2 v4 v5
du_sem'45'para_970 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
du_sem'45'para_970 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         du_sem'45'cata_954 v0 v1 (coe du_alg''_986 (coe v0) (coe v2)) v3)
-- Once.Semantics.Core._.alg'
d_alg''_986 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_alg''_986 ~v0 v1 ~v2 ~v3 v4 ~v5 v6 = du_alg''_986 v1 v4 v6
du_alg''_986 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_alg''_986 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_sem'45'In_934 (coe v0)
         (coe
            du_sem'45'fmap_432 (coe v0)
            (coe (\ v3 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
            (coe v2)))
      (coe v1 v2)
-- Once.Semantics.Core.coerce-ν-in
d_coerce'45'ν'45'in_994 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_994 ~v0 = du_coerce'45'ν'45'in_994
du_coerce'45'ν'45'in_994 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> AgdaAny -> AgdaAny
du_coerce'45'ν'45'in_994 v0 v1 v2
  = coe du_coerce'45'μ'45'in_760 v0 v2
-- Once.Semantics.Core.coerce-ν-out
d_coerce'45'ν'45'out_1000 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_1000 ~v0 v1 = du_coerce'45'ν'45'out_1000 v1
du_coerce'45'ν'45'out_1000 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () -> AgdaAny -> AgdaAny
du_coerce'45'ν'45'out_1000 v0 v1 v2 v3
  = coe du_coerce'45'μ'45'out_802 (coe v0) v1 v3
-- Once.Semantics.Core.sem-CoOut
d_sem'45'CoOut_1004 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 -> AgdaAny
d_sem'45'CoOut_1004 ~v0 v1 v2 v3 = du_sem'45'CoOut_1004 v1 v2 v3
du_sem'45'CoOut_1004 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 -> AgdaAny
du_sem'45'CoOut_1004 v0 v1 v2
  = coe
      du_coerce'45'ν'45'out_1000 v0 v1 erased
      (MAlonzo.Code.Once.Functor.Base.d_unfoldS_252 (coe v2))
-- Once.Semantics.Core.sem-CoIn
d_sem'45'CoIn_1014 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_νS_246
d_sem'45'CoIn_1014 ~v0 v1 v2 = du_sem'45'CoIn_1014 v1 v2
du_sem'45'CoIn_1014 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_νS_246
du_sem'45'CoIn_1014 v0 v1
  = coe
      MAlonzo.Code.Once.Functor.Base.C_constructor_254
      (coe du_coerce'45'ν'45'in_994 v0 erased v1)
-- Once.Semantics.Core.sem-CoOut-CoIn
d_sem'45'CoOut'45'CoIn_1026 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoOut'45'CoIn_1026 = erased
-- Once.Semantics.Core.∼S-refl-at
d_'8764'S'45'refl'45'at_1038 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Once.Functor.Base.T__'8764'S__738
d_'8764'S'45'refl'45'at_1038 ~v0 v1 v2
  = du_'8764'S'45'refl'45'at_1038 v1 v2
du_'8764'S'45'refl'45'at_1038 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Once.Functor.Base.T__'8764'S__738
du_'8764'S'45'refl'45'at_1038 v0 v1
  = coe
      MAlonzo.Code.Once.Functor.Base.C_constructor_750
      (coe
         du_sfmap'45''8764'S'45'refl_1046 (coe v0)
         (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_38 (coe v0))
         (coe MAlonzo.Code.Once.Functor.Base.d_unfoldS_252 (coe v1)))
-- Once.Semantics.Core.sfmap-∼S-refl
d_sfmap'45''8764'S'45'refl_1046 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Base.T_SFunctor_6 -> AgdaAny -> AgdaAny
d_sfmap'45''8764'S'45'refl_1046 ~v0 v1 v2 v3
  = du_sfmap'45''8764'S'45'refl_1046 v1 v2 v3
du_sfmap'45''8764'S'45'refl_1046 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Base.T_SFunctor_6 -> AgdaAny -> AgdaAny
du_sfmap'45''8764'S'45'refl_1046 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Base.C_SK_8 -> erased
      MAlonzo.Code.Once.Functor.Base.C_SId_10
        -> coe du_'8764'S'45'refl'45'at_1038 (coe v0) (coe v2)
      MAlonzo.Code.Once.Functor.Base.C__S'8853'__12 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe du_sfmap'45''8764'S'45'refl_1046 (coe v0) (coe v3) (coe v5)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe du_sfmap'45''8764'S'45'refl_1046 (coe v0) (coe v4) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Base.C__S'8855'__14 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sfmap'45''8764'S'45'refl_1046 (coe v0) (coe v3) (coe v5))
                    (coe du_sfmap'45''8764'S'45'refl_1046 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Core.CoIn-CoOut-bisim
d_CoIn'45'CoOut'45'bisim_1082 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Once.Functor.Base.T__'8764'S__738
d_CoIn'45'CoOut'45'bisim_1082 ~v0 v1 ~v2 v3
  = du_CoIn'45'CoOut'45'bisim_1082 v1 v3
du_CoIn'45'CoOut'45'bisim_1082 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Once.Functor.Base.T__'8764'S__738
du_CoIn'45'CoOut'45'bisim_1082 v0 v1
  = coe
      MAlonzo.Code.Once.Functor.Base.C_constructor_750
      (coe
         du_sfmap'45''8764'S'45'refl_1046 (coe v0)
         (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_38 (coe v0))
         (coe MAlonzo.Code.Once.Functor.Base.d_unfoldS_252 (coe v1)))
-- Once.Semantics.Core.sem-CoIn-CoOut
d_sem'45'CoIn'45'CoOut_1102 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoIn'45'CoOut_1102 = erased
-- Once.Semantics.Core.sem-ana
d_sem'45'ana_1114 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_νS_246
d_sem'45'ana_1114 ~v0 v1 ~v2 v3 v4 = du_sem'45'ana_1114 v1 v3 v4
du_sem'45'ana_1114 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_νS_246
du_sem'45'ana_1114 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Functor.Base.C_constructor_254
      (coe
         MAlonzo.Code.Once.Functor.Base.du_sfmap_42
         (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_38 (coe v0))
         (coe du_sem'45'ana_1114 (coe v0) (coe v1))
         (coe du_coerce'45'ν'45'in_994 v0 erased (coe v1 v2)))
-- Once.Semantics.Core.sem-fuse
d_sem'45'fuse_1130 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'fuse_1130 ~v0 v1 v2 v3 v4 ~v5 v6 v7
  = du_sem'45'fuse_1130 v1 v2 v3 v4 v6 v7
du_sem'45'fuse_1130 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
du_sem'45'fuse_1130 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Functor.Base.du_fuseS_642
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_38 (coe v0))
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_38 (coe v1))
      (coe
         (\ v6 ->
            coe v4 (coe du_coerce'45'μ'45'out_802 (coe v0) (coe v2) (coe v6))))
      (coe
         (\ v6 ->
            coe
              du_coerce'45'μ'45'in_760 (coe v0)
              (coe
                 v5 (coe du_coerce'45'μ'45'out_802 (coe v1) (coe v3) (coe v6)))))
-- Once.Semantics.Core.sem-fuseNat
d_sem'45'fuseNat_1154 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'fuseNat_1154 ~v0 v1 v2 v3 v4 ~v5 v6 v7
  = du_sem'45'fuseNat_1154 v1 v2 v3 v4 v6 v7
du_sem'45'fuseNat_1154 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
du_sem'45'fuseNat_1154 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Functor.Base.du_fuseNatS_548
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_38 (coe v1))
      erased
      (coe
         (\ v6 v7 ->
            coe
              du_coerce'45'μ'45'in_760 (coe v0)
              (coe
                 v4 v6 (coe du_coerce'45'μ'45'out_802 (coe v1) (coe v3) (coe v7)))))
      (coe
         (\ v6 ->
            coe v5 (coe du_coerce'45'μ'45'out_802 (coe v0) (coe v2) (coe v6))))
-- Once.Semantics.Core.sem-hylo
d_sem'45'hylo_1176 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'hylo_1176 ~v0 v1 v2 v3 v4 ~v5 v6 v7
  = du_sem'45'hylo_1176 v1 v2 v3 v4 v6 v7
du_sem'45'hylo_1176 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
du_sem'45'hylo_1176 v0 v1 v2 v3 v4 v5
  = coe
      du_sem'45'fuse_1130 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe (\ v6 -> coe v5 (coe du_sem'45'In_934 (coe v1) (coe v6))))
-- Once.Semantics.Core.sem-fuse-events
d_sem'45'fuse'45'events_1204 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'fuse'45'events_1204 ~v0 ~v1 v2 v3 v4 v5 v6 v7 ~v8 v9 v10
  = du_sem'45'fuse'45'events_1204 v2 v3 v4 v5 v6 v7 v9 v10
du_sem'45'fuse'45'events_1204 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sem'45'fuse'45'events_1204 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Functor.Base.du_fuseW_568
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_38 (coe v2))
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_38 (coe v3))
      (coe v0) (coe v1)
      (coe
         (\ v8 ->
            coe v6 (coe du_coerce'45'μ'45'out_802 (coe v2) (coe v4) (coe v8))))
      (coe
         (\ v8 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe
                    v7 (coe du_coerce'45'μ'45'out_802 (coe v3) (coe v5) (coe v8))))
              (coe
                 du_coerce'45'μ'45'in_760 (coe v2)
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                    (coe
                       v7 (coe du_coerce'45'μ'45'out_802 (coe v3) (coe v5) (coe v8)))))))
-- Once.Semantics.Core.sem-hylo-events
d_sem'45'hylo'45'events_1244 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'hylo'45'events_1244 ~v0 ~v1 v2 v3 v4 v5 v6 v7 ~v8 v9 v10
  = du_sem'45'hylo'45'events_1244 v2 v3 v4 v5 v6 v7 v9 v10
du_sem'45'hylo'45'events_1244 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sem'45'hylo'45'events_1244 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_sem'45'fuse'45'events_1204 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4) (coe v5) (coe v6)
      (coe (\ v8 -> coe v7 (coe du_sem'45'In_934 (coe v3) (coe v8))))
-- Once.Semantics.Core.sem-Out-In
d_sem'45'Out'45'In_1274 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'Out'45'In_1274 = erased
-- Once.Semantics.Core.sem-In-Out
d_sem'45'In'45'Out_1286 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'In'45'Out_1286 = erased
-- Once.Semantics.Core.fmap-coerce-μ-coherence
d_fmap'45'coerce'45'μ'45'coherence_1302 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence_1302 = erased
-- Once.Semantics.Core.fmap-coerce-μ-coherence′
d_fmap'45'coerce'45'μ'45'coherence'8242'_1352 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence'8242'_1352 = erased
-- Once.Semantics.Core.sem-cata-compute
d_sem'45'cata'45'compute_1400 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'compute_1400 = erased
-- Once.Semantics.Core.sem-cata-In-id
d_sem'45'cata'45'In'45'id_1434 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'In'45'id_1434 = erased
-- Once.Semantics.Core.coerce-ν-in-sem-CoOut
d_coerce'45'ν'45'in'45'sem'45'CoOut_1468 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'ν'45'in'45'sem'45'CoOut_1468 = erased
-- Once.Semantics.Core.sfmap-bisim
d_sfmap'45'bisim_1486 ::
  () ->
  MAlonzo.Code.Once.Functor.Base.T_SFunctor_6 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  (MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
   MAlonzo.Code.Once.Functor.Base.T_νS_246) ->
  (MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
   MAlonzo.Code.Once.Functor.Base.T_νS_246) ->
  (MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
   MAlonzo.Code.Once.Functor.Base.T__'8764'S__738) ->
  AgdaAny -> AgdaAny
d_sfmap'45'bisim_1486 ~v0 v1 ~v2 ~v3 ~v4 v5 v6
  = du_sfmap'45'bisim_1486 v1 v5 v6
du_sfmap'45'bisim_1486 ::
  MAlonzo.Code.Once.Functor.Base.T_SFunctor_6 ->
  (MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
   MAlonzo.Code.Once.Functor.Base.T__'8764'S__738) ->
  AgdaAny -> AgdaAny
du_sfmap'45'bisim_1486 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Functor.Base.C_SK_8 -> erased
      MAlonzo.Code.Once.Functor.Base.C_SId_10 -> coe v1 v2
      MAlonzo.Code.Once.Functor.Base.C__S'8853'__12 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe du_sfmap'45'bisim_1486 (coe v3) (coe v1) (coe v5)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe du_sfmap'45'bisim_1486 (coe v4) (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Base.C__S'8855'__14 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sfmap'45'bisim_1486 (coe v3) (coe v1) (coe v5))
                    (coe du_sfmap'45'bisim_1486 (coe v4) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Core.sem-ana-bisim-anaS
d_sem'45'ana'45'bisim'45'anaS_1548 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Once.Functor.Base.T__'8764'S__738
d_sem'45'ana'45'bisim'45'anaS_1548 ~v0 v1 ~v2 v3
  = du_sem'45'ana'45'bisim'45'anaS_1548 v1 v3
du_sem'45'ana'45'bisim'45'anaS_1548 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Once.Functor.Base.T__'8764'S__738
du_sem'45'ana'45'bisim'45'anaS_1548 v0 v1
  = coe
      MAlonzo.Code.Once.Functor.Base.C_constructor_750
      (coe
         du_sfmap'45'bisim_1486
         (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_38 (coe v0))
         (coe du_sem'45'ana'45'bisim'45'anaS_1548 (coe v0))
         (coe MAlonzo.Code.Once.Functor.Base.d_unfoldS_252 (coe v1)))
-- Once.Semantics.Core.sem-ana-is-anaS-unfoldS
d_sem'45'ana'45'is'45'anaS'45'unfoldS_1568 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'ana'45'is'45'anaS'45'unfoldS_1568 = erased
-- Once.Semantics.Core.sem-ana-Out-id
d_sem'45'ana'45'Out'45'id_1580 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'ana'45'Out'45'id_1580 = erased
-- Once.Semantics.Core.sem-hylo-is-fuse
d_sem'45'hylo'45'is'45'fuse_1604 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_174 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'hylo'45'is'45'fuse_1604 = erased
