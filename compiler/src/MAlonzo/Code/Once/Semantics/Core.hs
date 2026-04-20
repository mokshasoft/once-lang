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
  () -> MAlonzo.Code.Once.Type.T_Functor_36 -> ()
d_'10214'μ'10215'_22 = erased
-- Once.Semantics.Core.⟦ν⟧
d_'10214'ν'10215'_24 ::
  () -> MAlonzo.Code.Once.Type.T_Functor_36 -> ()
d_'10214'ν'10215'_24 = erased
-- Once.Semantics.Core.⟦_⟧
d_'10214'_'10215'_26 ::
  () -> MAlonzo.Code.Once.Type.T_Type_38 -> ()
d_'10214'_'10215'_26 = erased
-- Once.Semantics.Core.⟦_⟧F
d_'10214'_'10215'F_48 ::
  () -> MAlonzo.Code.Once.Type.T_Functor_36 -> () -> ()
d_'10214'_'10215'F_48 = erased
-- Once.Semantics.Core.sem-functor-coherence
d_sem'45'functor'45'coherence_72 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'functor'45'coherence_72 = erased
-- Once.Semantics.Core.coerce-functor
d_coerce'45'functor_112 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Type_38 -> AgdaAny -> AgdaAny
d_coerce'45'functor_112 ~v0 v1 ~v2 v3
  = du_coerce'45'functor_112 v1 v3
du_coerce'45'functor_112 ::
  MAlonzo.Code.Once.Type.T_Functor_36 -> AgdaAny -> AgdaAny
du_coerce'45'functor_112 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_40 v2 -> coe v1
      MAlonzo.Code.Once.Type.C_Id_42 -> coe v1
      MAlonzo.Code.Once.Type.C__'8853'__44 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coerce'45'functor_112 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coerce'45'functor_112 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__46 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coerce'45'functor_112 (coe v2) (coe v4))
                    (coe du_coerce'45'functor_112 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Core.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_154 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Type_38 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_154 ~v0 v1 ~v2 v3
  = du_coerce'45'functor'8315''185'_154 v1 v3
du_coerce'45'functor'8315''185'_154 ::
  MAlonzo.Code.Once.Type.T_Functor_36 -> AgdaAny -> AgdaAny
du_coerce'45'functor'8315''185'_154 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_40 v2 -> coe v1
      MAlonzo.Code.Once.Type.C_Id_42 -> coe v1
      MAlonzo.Code.Once.Type.C__'8853'__44 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coerce'45'functor'8315''185'_154 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coerce'45'functor'8315''185'_154 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__46 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coerce'45'functor'8315''185'_154 (coe v2) (coe v4))
                    (coe du_coerce'45'functor'8315''185'_154 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Core.coerce-round-trip
d_coerce'45'round'45'trip_198 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'round'45'trip_198 = erased
-- Once.Semantics.Core.coerce⁻¹-round-trip
d_coerce'8315''185''45'round'45'trip_242 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'8315''185''45'round'45'trip_242 = erased
-- Once.Semantics.Core.coerce-struct
d_coerce'45'struct_284 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Type_38 -> AgdaAny -> AgdaAny
d_coerce'45'struct_284 ~v0 = du_coerce'45'struct_284
du_coerce'45'struct_284 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Type_38 -> AgdaAny -> AgdaAny
du_coerce'45'struct_284 v0 v1 v2
  = coe du_coerce'45'functor_112 v0 v2
-- Once.Semantics.Core.coerce-struct⁻¹
d_coerce'45'struct'8315''185'_290 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Type_38 -> AgdaAny -> AgdaAny
d_coerce'45'struct'8315''185'_290 ~v0
  = du_coerce'45'struct'8315''185'_290
du_coerce'45'struct'8315''185'_290 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Type_38 -> AgdaAny -> AgdaAny
du_coerce'45'struct'8315''185'_290 v0 v1 v2
  = coe du_coerce'45'functor'8315''185'_154 v0 v2
-- Once.Semantics.Core.coerce-struct-round-trip
d_coerce'45'struct'45'round'45'trip_298 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'45'round'45'trip_298 = erased
-- Once.Semantics.Core.coerce-struct⁻¹-round-trip
d_coerce'45'struct'8315''185''45'round'45'trip_306 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'8315''185''45'round'45'trip_306 = erased
-- Once.Semantics.Core.sem-fst
d_sem'45'fst_312 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'fst_312 ~v0 ~v1 ~v2 v3 = du_sem'45'fst_312 v3
du_sem'45'fst_312 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_sem'45'fst_312 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)
-- Once.Semantics.Core.sem-snd
d_sem'45'snd_318 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'snd_318 ~v0 ~v1 ~v2 v3 = du_sem'45'snd_318 v3
du_sem'45'snd_318 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_sem'45'snd_318 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)
-- Once.Semantics.Core.sem-pair
d_sem'45'pair_324 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'pair_324 ~v0 ~v1 ~v2 v3 v4 = du_sem'45'pair_324 v3 v4
du_sem'45'pair_324 ::
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sem'45'pair_324 v0 v1
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
-- Once.Semantics.Core.sem-inl
d_sem'45'inl_334 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inl_334 ~v0 ~v1 ~v2 = du_sem'45'inl_334
du_sem'45'inl_334 ::
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sem'45'inl_334 = coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
-- Once.Semantics.Core.sem-inr
d_sem'45'inr_340 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inr_340 ~v0 ~v1 ~v2 = du_sem'45'inr_340
du_sem'45'inr_340 ::
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sem'45'inr_340 = coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
-- Once.Semantics.Core.sem-case
d_sem'45'case_348 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_sem'45'case_348 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_sem'45'case_348 v4 v5 v6
du_sem'45'case_348 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_sem'45'case_348 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> coe v0 v3
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3 -> coe v1 v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Core.sem-fst-pair
d_sem'45'fst'45'pair_370 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fst'45'pair_370 = erased
-- Once.Semantics.Core.sem-snd-pair
d_sem'45'snd'45'pair_384 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'snd'45'pair_384 = erased
-- Once.Semantics.Core.sem-case-inl
d_sem'45'case'45'inl_402 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inl_402 = erased
-- Once.Semantics.Core.sem-case-inr
d_sem'45'case'45'inr_422 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inr_422 = erased
-- Once.Semantics.Core.sem-fmap
d_sem'45'fmap_436 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_436 ~v0 v1 ~v2 ~v3 v4 v5
  = du_sem'45'fmap_436 v1 v4 v5
du_sem'45'fmap_436 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_sem'45'fmap_436 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_40 v3 -> coe v2
      MAlonzo.Code.Once.Type.C_Id_42 -> coe v1 v2
      MAlonzo.Code.Once.Type.C__'8853'__44 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_sem'45'fmap_436 (coe v3) (coe v1) (coe v5))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_sem'45'fmap_436 (coe v4) (coe v1) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__46 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sem'45'fmap_436 (coe v3) (coe v1) (coe v5))
                    (coe du_sem'45'fmap_436 (coe v4) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Core.sem-fmap-Type
d_sem'45'fmap'45'Type_480 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap'45'Type_480 ~v0 v1 ~v2 ~v3 v4 v5
  = du_sem'45'fmap'45'Type_480 v1 v4 v5
du_sem'45'fmap'45'Type_480 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_sem'45'fmap'45'Type_480 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_40 v3 -> coe v2
      MAlonzo.Code.Once.Type.C_Id_42 -> coe v1 v2
      MAlonzo.Code.Once.Type.C__'8853'__44 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_sem'45'fmap'45'Type_480 (coe v3) (coe v1) (coe v5))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_sem'45'fmap'45'Type_480 (coe v4) (coe v1) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__46 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sem'45'fmap'45'Type_480 (coe v3) (coe v1) (coe v5))
                    (coe du_sem'45'fmap'45'Type_480 (coe v4) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Core.fmap-struct-coherence
d_fmap'45'struct'45'coherence_528 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence_528 = erased
-- Once.Semantics.Core.fmap-struct-coherence′
d_fmap'45'struct'45'coherence'8242'_576 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence'8242'_576 = erased
-- Once.Semantics.Core.coerce-full-to-base
d_coerce'45'full'45'to'45'base_616 ::
  () -> MAlonzo.Code.Once.Type.T_Type_38 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_616 ~v0 v1 v2
  = du_coerce'45'full'45'to'45'base_616 v1 v2
du_coerce'45'full'45'to'45'base_616 ::
  MAlonzo.Code.Once.Type.T_Type_38 -> AgdaAny -> AgdaAny
du_coerce'45'full'45'to'45'base_616 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_48 -> coe v1
      MAlonzo.Code.Once.Type.C_Void_50 -> coe v1
      MAlonzo.Code.Once.Type.C__'42'__52 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coerce'45'full'45'to'45'base_616 (coe v2) (coe v4))
                    (coe du_coerce'45'full'45'to'45'base_616 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'43'__54 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coerce'45'full'45'to'45'base_616 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coerce'45'full'45'to'45'base_616 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__56 v2 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Type.C_Eff_58 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Type.C_μ'45'type_60 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Type.C_ν'45'type_62 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Type.C_Int_64 -> coe v1
      MAlonzo.Code.Once.Type.C_Float_66 -> coe v1
      MAlonzo.Code.Once.Type.C_Str_68 -> coe v1
      MAlonzo.Code.Once.Type.C_Buffer_70 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Core.coerce-base-to-full
d_coerce'45'base'45'to'45'full_652 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_150 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_652 ~v0 v1 v2 v3
  = du_coerce'45'base'45'to'45'full_652 v1 v2 v3
du_coerce'45'base'45'to'45'full_652 ::
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_150 ->
  AgdaAny -> AgdaAny
du_coerce'45'base'45'to'45'full_652 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_152 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_156 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_158 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Str_160 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Buffer_162 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_168 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'42'__52 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              du_coerce'45'base'45'to'45'full_652 (coe v7) (coe v5) (coe v9))
                           (coe
                              du_coerce'45'base'45'to'45'full_652 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_174 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__54 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe
                              du_coerce'45'base'45'to'45'full_652 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe
                              du_coerce'45'base'45'to'45'full_652 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Core.coerce-base-type-round-trip
d_coerce'45'base'45'type'45'round'45'trip_690 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_150 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'45'round'45'trip_690 = erased
-- Once.Semantics.Core.coerce-base-type⁻¹-round-trip
d_coerce'45'base'45'type'8315''185''45'round'45'trip_728 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_38 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_150 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'8315''185''45'round'45'trip_728 = erased
-- Once.Semantics.Core.coerce-μ-in
d_coerce'45'μ'45'in_764 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_764 ~v0 v1 ~v2 v3
  = du_coerce'45'μ'45'in_764 v1 v3
du_coerce'45'μ'45'in_764 ::
  MAlonzo.Code.Once.Type.T_Functor_36 -> AgdaAny -> AgdaAny
du_coerce'45'μ'45'in_764 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_40 v2
        -> coe du_coerce'45'full'45'to'45'base_616 (coe v2) (coe v1)
      MAlonzo.Code.Once.Type.C_Id_42 -> coe v1
      MAlonzo.Code.Once.Type.C__'8853'__44 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coerce'45'μ'45'in_764 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coerce'45'μ'45'in_764 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__46 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coerce'45'μ'45'in_764 (coe v2) (coe v4))
                    (coe du_coerce'45'μ'45'in_764 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Core.coerce-μ-out
d_coerce'45'μ'45'out_806 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_806 ~v0 v1 v2 ~v3 v4
  = du_coerce'45'μ'45'out_806 v1 v2 v4
du_coerce'45'μ'45'out_806 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  AgdaAny -> AgdaAny
du_coerce'45'μ'45'out_806 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_180 v4
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_K_40 v5
               -> coe
                    du_coerce'45'base'45'to'45'full_652 (coe v5) (coe v4) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_182 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_188 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__44 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe du_coerce'45'μ'45'out_806 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe du_coerce'45'μ'45'out_806 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_194 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__46 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe du_coerce'45'μ'45'out_806 (coe v7) (coe v5) (coe v9))
                           (coe du_coerce'45'μ'45'out_806 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Core.coerce-μ-round-trip
d_coerce'45'μ'45'round'45'trip_852 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'45'round'45'trip_852 = erased
-- Once.Semantics.Core.coerce-μ⁻¹-round-trip
d_coerce'45'μ'8315''185''45'round'45'trip_898 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'8315''185''45'round'45'trip_898 = erased
-- Once.Semantics.Core.sem-In
d_sem'45'In_938 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_μS_230
d_sem'45'In_938 ~v0 v1 v2 = du_sem'45'In_938 v1 v2
du_sem'45'In_938 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_μS_230
du_sem'45'In_938 v0 v1
  = coe
      MAlonzo.Code.Once.Functor.Base.C_'10216'_'10217'_234
      (coe du_coerce'45'μ'45'in_764 (coe v0) (coe v1))
-- Once.Semantics.Core.sem-Out
d_sem'45'Out_946 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'Out_946 ~v0 v1 v2 v3 = du_sem'45'Out_946 v1 v2 v3
du_sem'45'Out_946 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
du_sem'45'Out_946 v0 v1 v2
  = coe
      du_coerce'45'μ'45'out_806 (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.Functor.Base.d_outS_238 (coe v2))
-- Once.Semantics.Core.sem-cata
d_sem'45'cata_958 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'cata_958 ~v0 v1 v2 ~v3 v4 = du_sem'45'cata_958 v1 v2 v4
du_sem'45'cata_958 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
du_sem'45'cata_958 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Functor.Base.du_cataS_260
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_40 (coe v0))
      (coe
         (\ v3 ->
            coe v2 (coe du_coerce'45'μ'45'out_806 (coe v0) (coe v1) (coe v3))))
-- Once.Semantics.Core.sem-para
d_sem'45'para_974 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'para_974 ~v0 v1 v2 ~v3 v4 v5
  = du_sem'45'para_974 v1 v2 v4 v5
du_sem'45'para_974 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
du_sem'45'para_974 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         du_sem'45'cata_958 v0 v1 (coe du_alg''_990 (coe v0) (coe v2)) v3)
-- Once.Semantics.Core._.alg'
d_alg''_990 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_alg''_990 ~v0 v1 ~v2 ~v3 v4 ~v5 v6 = du_alg''_990 v1 v4 v6
du_alg''_990 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_alg''_990 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_sem'45'In_938 (coe v0)
         (coe
            du_sem'45'fmap_436 (coe v0)
            (coe (\ v3 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
            (coe v2)))
      (coe v1 v2)
-- Once.Semantics.Core.coerce-ν-in
d_coerce'45'ν'45'in_998 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_998 ~v0 = du_coerce'45'ν'45'in_998
du_coerce'45'ν'45'in_998 ::
  MAlonzo.Code.Once.Type.T_Functor_36 -> () -> AgdaAny -> AgdaAny
du_coerce'45'ν'45'in_998 v0 v1 v2
  = coe du_coerce'45'μ'45'in_764 v0 v2
-- Once.Semantics.Core.coerce-ν-out
d_coerce'45'ν'45'out_1004 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_1004 ~v0 v1 = du_coerce'45'ν'45'out_1004 v1
du_coerce'45'ν'45'out_1004 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  () -> AgdaAny -> AgdaAny
du_coerce'45'ν'45'out_1004 v0 v1 v2 v3
  = coe du_coerce'45'μ'45'out_806 (coe v0) v1 v3
-- Once.Semantics.Core.sem-CoOut
d_sem'45'CoOut_1008 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 -> AgdaAny
d_sem'45'CoOut_1008 ~v0 v1 v2 v3 = du_sem'45'CoOut_1008 v1 v2 v3
du_sem'45'CoOut_1008 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 -> AgdaAny
du_sem'45'CoOut_1008 v0 v1 v2
  = coe
      du_coerce'45'ν'45'out_1004 v0 v1 erased
      (MAlonzo.Code.Once.Functor.Base.d_unfoldS_252 (coe v2))
-- Once.Semantics.Core.sem-CoIn
d_sem'45'CoIn_1018 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_νS_246
d_sem'45'CoIn_1018 ~v0 v1 v2 = du_sem'45'CoIn_1018 v1 v2
du_sem'45'CoIn_1018 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_νS_246
du_sem'45'CoIn_1018 v0 v1
  = coe
      MAlonzo.Code.Once.Functor.Base.C_constructor_254
      (coe du_coerce'45'ν'45'in_998 v0 erased v1)
-- Once.Semantics.Core.sem-CoOut-CoIn
d_sem'45'CoOut'45'CoIn_1030 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoOut'45'CoIn_1030 = erased
-- Once.Semantics.Core.∼S-refl-at
d_'8764'S'45'refl'45'at_1042 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Once.Functor.Base.T__'8764'S__688
d_'8764'S'45'refl'45'at_1042 ~v0 v1 v2
  = du_'8764'S'45'refl'45'at_1042 v1 v2
du_'8764'S'45'refl'45'at_1042 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Once.Functor.Base.T__'8764'S__688
du_'8764'S'45'refl'45'at_1042 v0 v1
  = coe
      MAlonzo.Code.Once.Functor.Base.C_constructor_700
      (coe
         du_sfmap'45''8764'S'45'refl_1050 (coe v0)
         (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_40 (coe v0))
         (coe MAlonzo.Code.Once.Functor.Base.d_unfoldS_252 (coe v1)))
-- Once.Semantics.Core.sfmap-∼S-refl
d_sfmap'45''8764'S'45'refl_1050 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Base.T_SFunctor_6 -> AgdaAny -> AgdaAny
d_sfmap'45''8764'S'45'refl_1050 ~v0 v1 v2 v3
  = du_sfmap'45''8764'S'45'refl_1050 v1 v2 v3
du_sfmap'45''8764'S'45'refl_1050 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Base.T_SFunctor_6 -> AgdaAny -> AgdaAny
du_sfmap'45''8764'S'45'refl_1050 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Base.C_SK_8 -> erased
      MAlonzo.Code.Once.Functor.Base.C_SId_10
        -> coe du_'8764'S'45'refl'45'at_1042 (coe v0) (coe v2)
      MAlonzo.Code.Once.Functor.Base.C__S'8853'__12 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe du_sfmap'45''8764'S'45'refl_1050 (coe v0) (coe v3) (coe v5)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe du_sfmap'45''8764'S'45'refl_1050 (coe v0) (coe v4) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Base.C__S'8855'__14 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sfmap'45''8764'S'45'refl_1050 (coe v0) (coe v3) (coe v5))
                    (coe du_sfmap'45''8764'S'45'refl_1050 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Core.CoIn-CoOut-bisim
d_CoIn'45'CoOut'45'bisim_1086 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Once.Functor.Base.T__'8764'S__688
d_CoIn'45'CoOut'45'bisim_1086 ~v0 v1 ~v2 v3
  = du_CoIn'45'CoOut'45'bisim_1086 v1 v3
du_CoIn'45'CoOut'45'bisim_1086 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Once.Functor.Base.T__'8764'S__688
du_CoIn'45'CoOut'45'bisim_1086 v0 v1
  = coe
      MAlonzo.Code.Once.Functor.Base.C_constructor_700
      (coe
         du_sfmap'45''8764'S'45'refl_1050 (coe v0)
         (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_40 (coe v0))
         (coe MAlonzo.Code.Once.Functor.Base.d_unfoldS_252 (coe v1)))
-- Once.Semantics.Core.sem-CoIn-CoOut
d_sem'45'CoIn'45'CoOut_1106 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoIn'45'CoOut_1106 = erased
-- Once.Semantics.Core.sem-ana
d_sem'45'ana_1118 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_νS_246
d_sem'45'ana_1118 ~v0 v1 ~v2 v3 v4 = du_sem'45'ana_1118 v1 v3 v4
du_sem'45'ana_1118 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Functor.Base.T_νS_246
du_sem'45'ana_1118 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Functor.Base.C_constructor_254
      (coe
         MAlonzo.Code.Once.Functor.Base.du_sfmap_42
         (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_40 (coe v0))
         (coe du_sem'45'ana_1118 (coe v0) (coe v1))
         (coe du_coerce'45'ν'45'in_998 v0 erased (coe v1 v2)))
-- Once.Semantics.Core.sem-fuse
d_sem'45'fuse_1134 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'fuse_1134 ~v0 v1 v2 v3 v4 ~v5 v6 v7
  = du_sem'45'fuse_1134 v1 v2 v3 v4 v6 v7
du_sem'45'fuse_1134 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
du_sem'45'fuse_1134 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Functor.Base.du_fuseS_566
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_40 (coe v0))
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_40 (coe v1))
      (coe
         (\ v6 ->
            coe v4 (coe du_coerce'45'μ'45'out_806 (coe v0) (coe v2) (coe v6))))
      (coe
         (\ v6 ->
            coe
              du_coerce'45'μ'45'in_764 (coe v0)
              (coe
                 v5 (coe du_coerce'45'μ'45'out_806 (coe v1) (coe v3) (coe v6)))))
-- Once.Semantics.Core.sem-fuseNat
d_sem'45'fuseNat_1158 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'fuseNat_1158 ~v0 v1 v2 v3 v4 ~v5 v6 v7
  = du_sem'45'fuseNat_1158 v1 v2 v3 v4 v6 v7
du_sem'45'fuseNat_1158 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
du_sem'45'fuseNat_1158 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Functor.Base.du_fuseNatS_548
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_40 (coe v1))
      erased
      (coe
         (\ v6 v7 ->
            coe
              du_coerce'45'μ'45'in_764 (coe v0)
              (coe
                 v4 v6 (coe du_coerce'45'μ'45'out_806 (coe v1) (coe v3) (coe v7)))))
      (coe
         (\ v6 ->
            coe v5 (coe du_coerce'45'μ'45'out_806 (coe v0) (coe v2) (coe v6))))
-- Once.Semantics.Core.sem-hylo
d_sem'45'hylo_1180 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
d_sem'45'hylo_1180 ~v0 v1 v2 v3 v4 ~v5 v6 v7
  = du_sem'45'hylo_1180 v1 v2 v3 v4 v6 v7
du_sem'45'hylo_1180 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny
du_sem'45'hylo_1180 v0 v1 v2 v3 v4 v5
  = coe
      du_sem'45'fuse_1134 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe (\ v6 -> coe v5 (coe du_sem'45'In_938 (coe v1) (coe v6))))
-- Once.Semantics.Core.sem-Out-In
d_sem'45'Out'45'In_1202 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'Out'45'In_1202 = erased
-- Once.Semantics.Core.sem-In-Out
d_sem'45'In'45'Out_1214 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'In'45'Out_1214 = erased
-- Once.Semantics.Core.fmap-coerce-μ-coherence
d_fmap'45'coerce'45'μ'45'coherence_1230 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence_1230 = erased
-- Once.Semantics.Core.fmap-coerce-μ-coherence′
d_fmap'45'coerce'45'μ'45'coherence'8242'_1280 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence'8242'_1280 = erased
-- Once.Semantics.Core.sem-cata-compute
d_sem'45'cata'45'compute_1328 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'compute_1328 = erased
-- Once.Semantics.Core.sem-cata-In-id
d_sem'45'cata'45'In'45'id_1362 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'In'45'id_1362 = erased
-- Once.Semantics.Core.coerce-ν-in-sem-CoOut
d_coerce'45'ν'45'in'45'sem'45'CoOut_1396 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'ν'45'in'45'sem'45'CoOut_1396 = erased
-- Once.Semantics.Core.sfmap-bisim
d_sfmap'45'bisim_1414 ::
  () ->
  MAlonzo.Code.Once.Functor.Base.T_SFunctor_6 ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  (MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
   MAlonzo.Code.Once.Functor.Base.T_νS_246) ->
  (MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
   MAlonzo.Code.Once.Functor.Base.T_νS_246) ->
  (MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
   MAlonzo.Code.Once.Functor.Base.T__'8764'S__688) ->
  AgdaAny -> AgdaAny
d_sfmap'45'bisim_1414 ~v0 v1 ~v2 ~v3 ~v4 v5 v6
  = du_sfmap'45'bisim_1414 v1 v5 v6
du_sfmap'45'bisim_1414 ::
  MAlonzo.Code.Once.Functor.Base.T_SFunctor_6 ->
  (MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
   MAlonzo.Code.Once.Functor.Base.T__'8764'S__688) ->
  AgdaAny -> AgdaAny
du_sfmap'45'bisim_1414 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Functor.Base.C_SK_8 -> erased
      MAlonzo.Code.Once.Functor.Base.C_SId_10 -> coe v1 v2
      MAlonzo.Code.Once.Functor.Base.C__S'8853'__12 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe du_sfmap'45'bisim_1414 (coe v3) (coe v1) (coe v5)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe du_sfmap'45'bisim_1414 (coe v4) (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Base.C__S'8855'__14 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sfmap'45'bisim_1414 (coe v3) (coe v1) (coe v5))
                    (coe du_sfmap'45'bisim_1414 (coe v4) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Core.sem-ana-bisim-anaS
d_sem'45'ana'45'bisim'45'anaS_1476 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Once.Functor.Base.T__'8764'S__688
d_sem'45'ana'45'bisim'45'anaS_1476 ~v0 v1 ~v2 v3
  = du_sem'45'ana'45'bisim'45'anaS_1476 v1 v3
du_sem'45'ana'45'bisim'45'anaS_1476 ::
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Once.Functor.Base.T__'8764'S__688
du_sem'45'ana'45'bisim'45'anaS_1476 v0 v1
  = coe
      MAlonzo.Code.Once.Functor.Base.C_constructor_700
      (coe
         du_sfmap'45'bisim_1414
         (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_40 (coe v0))
         (coe du_sem'45'ana'45'bisim'45'anaS_1476 (coe v0))
         (coe MAlonzo.Code.Once.Functor.Base.d_unfoldS_252 (coe v1)))
-- Once.Semantics.Core.sem-ana-is-anaS-unfoldS
d_sem'45'ana'45'is'45'anaS'45'unfoldS_1496 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'ana'45'is'45'anaS'45'unfoldS_1496 = erased
-- Once.Semantics.Core.sem-ana-Out-id
d_sem'45'ana'45'Out'45'id_1508 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Base.T_νS_246 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'ana'45'Out'45'id_1508 = erased
-- Once.Semantics.Core.sem-hylo-is-fuse
d_sem'45'hylo'45'is'45'fuse_1532 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Type.T_Functor_36 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_176 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Once.Functor.Base.T_μS_230 -> AgdaAny) ->
  MAlonzo.Code.Once.Functor.Base.T_μS_230 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'hylo'45'is'45'fuse_1532 = erased
