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
d_'10214'μ'10215'_8 ::
  () -> MAlonzo.Code.Once.Type.T_Functor_110 -> ()
d_'10214'μ'10215'_8 = erased
-- Once.Semantics.Value.⟦ν⟧
d_'10214'ν'10215'_10 ::
  () -> MAlonzo.Code.Once.Type.T_Functor_110 -> ()
d_'10214'ν'10215'_10 = erased
-- Once.Semantics.Value.⟦_⟧
d_'10214'_'10215'_12 ::
  () -> MAlonzo.Code.Once.Type.T_Type_112 -> ()
d_'10214'_'10215'_12 = erased
-- Once.Semantics.Value.⟦_⟧F
d_'10214'_'10215'F_30 ::
  () -> MAlonzo.Code.Once.Type.T_Functor_110 -> () -> ()
d_'10214'_'10215'F_30 = erased
-- Once.Semantics.Value.sem-functor-coherence
d_sem'45'functor'45'coherence_54 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'functor'45'coherence_54 = erased
-- Once.Semantics.Value.coerce-functor
d_coerce'45'functor_94 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'functor_94 ~v0 v1 ~v2 v3
  = du_coerce'45'functor_94 v1 v3
du_coerce'45'functor_94 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> AgdaAny -> AgdaAny
du_coerce'45'functor_94 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_114 v2 -> coe v1
      MAlonzo.Code.Once.Type.C_Id_116 -> coe v1
      MAlonzo.Code.Once.Type.C__'8853'__118 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coerce'45'functor_94 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coerce'45'functor_94 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__120 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coerce'45'functor_94 (coe v2) (coe v4))
                    (coe du_coerce'45'functor_94 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_136 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_136 ~v0 v1 ~v2 v3
  = du_coerce'45'functor'8315''185'_136 v1 v3
du_coerce'45'functor'8315''185'_136 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> AgdaAny -> AgdaAny
du_coerce'45'functor'8315''185'_136 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_114 v2 -> coe v1
      MAlonzo.Code.Once.Type.C_Id_116 -> coe v1
      MAlonzo.Code.Once.Type.C__'8853'__118 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coerce'45'functor'8315''185'_136 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coerce'45'functor'8315''185'_136 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__120 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coerce'45'functor'8315''185'_136 (coe v2) (coe v4))
                    (coe du_coerce'45'functor'8315''185'_136 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.coerce-round-trip
d_coerce'45'round'45'trip_180 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'round'45'trip_180 = erased
-- Once.Semantics.Value.coerce⁻¹-round-trip
d_coerce'8315''185''45'round'45'trip_224 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'8315''185''45'round'45'trip_224 = erased
-- Once.Semantics.Value.coerce-struct
d_coerce'45'struct_266 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'struct_266 ~v0 = du_coerce'45'struct_266
du_coerce'45'struct_266 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
du_coerce'45'struct_266 v0 v1 v2
  = coe du_coerce'45'functor_94 v0 v2
-- Once.Semantics.Value.coerce-struct⁻¹
d_coerce'45'struct'8315''185'_272 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'struct'8315''185'_272 ~v0
  = du_coerce'45'struct'8315''185'_272
du_coerce'45'struct'8315''185'_272 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
du_coerce'45'struct'8315''185'_272 v0 v1 v2
  = coe du_coerce'45'functor'8315''185'_136 v0 v2
-- Once.Semantics.Value.coerce-struct-round-trip
d_coerce'45'struct'45'round'45'trip_280 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'45'round'45'trip_280 = erased
-- Once.Semantics.Value.coerce-struct⁻¹-round-trip
d_coerce'45'struct'8315''185''45'round'45'trip_288 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'struct'8315''185''45'round'45'trip_288 = erased
-- Once.Semantics.Value.sem-fst
d_sem'45'fst_294 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'fst_294 ~v0 ~v1 ~v2 v3 = du_sem'45'fst_294 v3
du_sem'45'fst_294 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_sem'45'fst_294 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)
-- Once.Semantics.Value.sem-snd
d_sem'45'snd_300 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_sem'45'snd_300 ~v0 ~v1 ~v2 v3 = du_sem'45'snd_300 v3
du_sem'45'snd_300 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_sem'45'snd_300 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0)
-- Once.Semantics.Value.sem-pair
d_sem'45'pair_306 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'pair_306 ~v0 ~v1 ~v2 v3 v4 = du_sem'45'pair_306 v3 v4
du_sem'45'pair_306 ::
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sem'45'pair_306 v0 v1
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)
-- Once.Semantics.Value.sem-inl
d_sem'45'inl_316 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inl_316 ~v0 ~v1 ~v2 = du_sem'45'inl_316
du_sem'45'inl_316 ::
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sem'45'inl_316 = coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
-- Once.Semantics.Value.sem-inr
d_sem'45'inr_322 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sem'45'inr_322 ~v0 ~v1 ~v2 = du_sem'45'inr_322
du_sem'45'inr_322 ::
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sem'45'inr_322 = coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
-- Once.Semantics.Value.sem-case
d_sem'45'case_330 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_sem'45'case_330 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_sem'45'case_330 v4 v5 v6
du_sem'45'case_330 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_sem'45'case_330 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> coe v0 v3
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3 -> coe v1 v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.sem-fst-pair
d_sem'45'fst'45'pair_352 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'fst'45'pair_352 = erased
-- Once.Semantics.Value.sem-snd-pair
d_sem'45'snd'45'pair_366 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'snd'45'pair_366 = erased
-- Once.Semantics.Value.sem-case-inl
d_sem'45'case'45'inl_384 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inl_384 = erased
-- Once.Semantics.Value.sem-case-inr
d_sem'45'case'45'inr_404 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'case'45'inr_404 = erased
-- Once.Semantics.Value.sem-fmap
d_sem'45'fmap_418 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_418 ~v0 v1 ~v2 ~v3 v4 v5
  = du_sem'45'fmap_418 v1 v4 v5
du_sem'45'fmap_418 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_sem'45'fmap_418 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_114 v3 -> coe v2
      MAlonzo.Code.Once.Type.C_Id_116 -> coe v1 v2
      MAlonzo.Code.Once.Type.C__'8853'__118 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_sem'45'fmap_418 (coe v3) (coe v1) (coe v5))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_sem'45'fmap_418 (coe v4) (coe v1) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__120 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sem'45'fmap_418 (coe v3) (coe v1) (coe v5))
                    (coe du_sem'45'fmap_418 (coe v4) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.sem-fmap-Type
d_sem'45'fmap'45'Type_462 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap'45'Type_462 ~v0 v1 ~v2 ~v3 v4 v5
  = du_sem'45'fmap'45'Type_462 v1 v4 v5
du_sem'45'fmap'45'Type_462 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_sem'45'fmap'45'Type_462 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_114 v3 -> coe v2
      MAlonzo.Code.Once.Type.C_Id_116 -> coe v1 v2
      MAlonzo.Code.Once.Type.C__'8853'__118 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_sem'45'fmap'45'Type_462 (coe v3) (coe v1) (coe v5))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_sem'45'fmap'45'Type_462 (coe v4) (coe v1) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__120 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sem'45'fmap'45'Type_462 (coe v3) (coe v1) (coe v5))
                    (coe du_sem'45'fmap'45'Type_462 (coe v4) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.fmap-struct-coherence
d_fmap'45'struct'45'coherence_510 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence_510 = erased
-- Once.Semantics.Value.fmap-struct-coherence′
d_fmap'45'struct'45'coherence'8242'_558 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'struct'45'coherence'8242'_558 = erased
-- Once.Semantics.Value.coerce-full-to-base
d_coerce'45'full'45'to'45'base_598 ::
  () -> MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_598 ~v0 v1 v2
  = du_coerce'45'full'45'to'45'base_598 v1 v2
du_coerce'45'full'45'to'45'base_598 ::
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
du_coerce'45'full'45'to'45'base_598 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_122 -> coe v1
      MAlonzo.Code.Once.Type.C_Void_124 -> coe v1
      MAlonzo.Code.Once.Type.C__'42'__126 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coerce'45'full'45'to'45'base_598 (coe v2) (coe v4))
                    (coe du_coerce'45'full'45'to'45'base_598 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'43'__128 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coerce'45'full'45'to'45'base_598 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coerce'45'full'45'to'45'base_598 (coe v3) (coe v4))
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
-- Once.Semantics.Value.coerce-base-to-full
d_coerce'45'base'45'to'45'full_634 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_634 ~v0 v1 v2 v3
  = du_coerce'45'base'45'to'45'full_634 v1 v2 v3
du_coerce'45'base'45'to'45'full_634 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> AgdaAny
du_coerce'45'base'45'to'45'full_634 v0 v1 v2
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
                              du_coerce'45'base'45'to'45'full_634 (coe v7) (coe v5) (coe v9))
                           (coe
                              du_coerce'45'base'45'to'45'full_634 (coe v8) (coe v6) (coe v10))
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
                              du_coerce'45'base'45'to'45'full_634 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe
                              du_coerce'45'base'45'to'45'full_634 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.coerce-base-type-round-trip
d_coerce'45'base'45'type'45'round'45'trip_672 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'45'round'45'trip_672 = erased
-- Once.Semantics.Value.coerce-base-type⁻¹-round-trip
d_coerce'45'base'45'type'8315''185''45'round'45'trip_710 ::
  () ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'base'45'type'8315''185''45'round'45'trip_710 = erased
-- Once.Semantics.Value.coerce-μ-in
d_coerce'45'μ'45'in_746 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_746 ~v0 v1 ~v2 v3
  = du_coerce'45'μ'45'in_746 v1 v3
du_coerce'45'μ'45'in_746 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> AgdaAny -> AgdaAny
du_coerce'45'μ'45'in_746 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_114 v2
        -> coe du_coerce'45'full'45'to'45'base_598 (coe v2) (coe v1)
      MAlonzo.Code.Once.Type.C_Id_116 -> coe v1
      MAlonzo.Code.Once.Type.C__'8853'__118 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_coerce'45'μ'45'in_746 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_coerce'45'μ'45'in_746 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__120 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_coerce'45'μ'45'in_746 (coe v2) (coe v4))
                    (coe du_coerce'45'μ'45'in_746 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.coerce-μ-out
d_coerce'45'μ'45'out_788 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_788 ~v0 v1 v2 ~v3 v4
  = du_coerce'45'μ'45'out_788 v1 v2 v4
du_coerce'45'μ'45'out_788 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  AgdaAny -> AgdaAny
du_coerce'45'μ'45'out_788 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_192 v4
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_K_114 v5
               -> coe
                    du_coerce'45'base'45'to'45'full_634 (coe v5) (coe v4) (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_194 -> coe v2
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_200 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe du_coerce'45'μ'45'out_788 (coe v7) (coe v5) (coe v9))
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe du_coerce'45'μ'45'out_788 (coe v8) (coe v6) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_206 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe du_coerce'45'μ'45'out_788 (coe v7) (coe v5) (coe v9))
                           (coe du_coerce'45'μ'45'out_788 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.coerce-μ-round-trip
d_coerce'45'μ'45'round'45'trip_834 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'45'round'45'trip_834 = erased
-- Once.Semantics.Value.coerce-μ⁻¹-round-trip
d_coerce'45'μ'8315''185''45'round'45'trip_880 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_coerce'45'μ'8315''185''45'round'45'trip_880 = erased
-- Once.Semantics.Value.sem-In
d_sem'45'In_920 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_μS_182
d_sem'45'In_920 ~v0 v1 v2 = du_sem'45'In_920 v1 v2
du_sem'45'In_920 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_μS_182
du_sem'45'In_920 v0 v1
  = coe
      MAlonzo.Code.Once.Semantics.Functor.C_'10216'_'10217'_186
      (coe du_coerce'45'μ'45'in_746 (coe v0) (coe v1))
-- Once.Semantics.Value.sem-Out
d_sem'45'Out_928 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'Out_928 ~v0 v1 v2 v3 = du_sem'45'Out_928 v1 v2 v3
du_sem'45'Out_928 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
du_sem'45'Out_928 v0 v1 v2
  = coe
      du_coerce'45'μ'45'out_788 (coe v0) (coe v1)
      (coe MAlonzo.Code.Once.Semantics.Functor.d_outS_190 (coe v2))
-- Once.Semantics.Value.sem-cata
d_sem'45'cata_940 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'cata_940 ~v0 v1 v2 ~v3 v4 = du_sem'45'cata_940 v1 v2 v4
du_sem'45'cata_940 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
du_sem'45'cata_940 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Functor.du_cataS_212
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_38 (coe v0))
      (coe
         (\ v3 ->
            coe v2 (coe du_coerce'45'μ'45'out_788 (coe v0) (coe v1) (coe v3))))
-- Once.Semantics.Value.sem-para
d_sem'45'para_956 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'para_956 ~v0 v1 v2 ~v3 v4 v5
  = du_sem'45'para_956 v1 v2 v4 v5
du_sem'45'para_956 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
du_sem'45'para_956 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         du_sem'45'cata_940 v0 v1 (coe du_alg''_972 (coe v0) (coe v2)) v3)
-- Once.Semantics.Value._.alg'
d_alg''_972 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_alg''_972 ~v0 v1 ~v2 ~v3 v4 ~v5 v6 = du_alg''_972 v1 v4 v6
du_alg''_972 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_alg''_972 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_sem'45'In_920 (coe v0)
         (coe
            du_sem'45'fmap_418 (coe v0)
            (coe (\ v3 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
            (coe v2)))
      (coe v1 v2)
-- Once.Semantics.Value.coerce-ν-in
d_coerce'45'ν'45'in_980 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_980 ~v0 = du_coerce'45'ν'45'in_980
du_coerce'45'ν'45'in_980 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> () -> AgdaAny -> AgdaAny
du_coerce'45'ν'45'in_980 v0 v1 v2
  = coe du_coerce'45'μ'45'in_746 v0 v2
-- Once.Semantics.Value.coerce-ν-out
d_coerce'45'ν'45'out_986 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_986 ~v0 v1 = du_coerce'45'ν'45'out_986 v1
du_coerce'45'ν'45'out_986 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  () -> AgdaAny -> AgdaAny
du_coerce'45'ν'45'out_986 v0 v1 v2 v3
  = coe du_coerce'45'μ'45'out_788 (coe v0) v1 v3
-- Once.Semantics.Value.sem-CoOut
d_sem'45'CoOut_990 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 -> AgdaAny
d_sem'45'CoOut_990 ~v0 v1 v2 v3 = du_sem'45'CoOut_990 v1 v2 v3
du_sem'45'CoOut_990 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 -> AgdaAny
du_sem'45'CoOut_990 v0 v1 v2
  = coe
      du_coerce'45'ν'45'out_986 v0 v1 erased
      (MAlonzo.Code.Once.Semantics.Functor.d_unfoldS_204 (coe v2))
-- Once.Semantics.Value.sem-CoIn
d_sem'45'CoIn_1000 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_sem'45'CoIn_1000 ~v0 v1 v2 = du_sem'45'CoIn_1000 v1 v2
du_sem'45'CoIn_1000 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
du_sem'45'CoIn_1000 v0 v1
  = coe
      MAlonzo.Code.Once.Semantics.Functor.C_constructor_206
      (coe du_coerce'45'ν'45'in_980 v0 erased v1)
-- Once.Semantics.Value.sem-CoOut-CoIn
d_sem'45'CoOut'45'CoIn_1012 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'CoOut'45'CoIn_1012 = erased
-- Once.Semantics.Value.sem-ana
d_sem'45'ana_1024 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
d_sem'45'ana_1024 ~v0 v1 ~v2 v3 v4 = du_sem'45'ana_1024 v1 v3 v4
du_sem'45'ana_1024 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_νS_198
du_sem'45'ana_1024 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Semantics.Functor.C_constructor_206
      (coe
         du_sfmapSemAna_1032 (coe v0)
         (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_38 (coe v0))
         (coe v1) (coe du_coerce'45'ν'45'in_980 v0 erased (coe v1 v2)))
-- Once.Semantics.Value.sfmapSemAna
d_sfmapSemAna_1032 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sfmapSemAna_1032 ~v0 v1 v2 ~v3 v4 v5
  = du_sfmapSemAna_1032 v1 v2 v4 v5
du_sfmapSemAna_1032 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_sfmapSemAna_1032 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Semantics.Functor.C_SK_8 -> coe v3
      MAlonzo.Code.Once.Semantics.Functor.C_SId_10
        -> coe du_sem'45'ana_1024 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.Semantics.Functor.C__S'8853'__12 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_sfmapSemAna_1032 (coe v0) (coe v4) (coe v2) (coe v6))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_sfmapSemAna_1032 (coe v0) (coe v5) (coe v2) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Semantics.Functor.C__S'8855'__14 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sfmapSemAna_1032 (coe v0) (coe v4) (coe v2) (coe v6))
                    (coe du_sfmapSemAna_1032 (coe v0) (coe v5) (coe v2) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Value.sfmapSemAna-is-sfmap
d_sfmapSemAna'45'is'45'sfmap_1098 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmapSemAna'45'is'45'sfmap_1098 = erased
-- Once.Semantics.Value.sem-fuseNat
d_sem'45'fuseNat_1154 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_sem'45'fuseNat_1154 ~v0 v1 v2 v3 v4 ~v5 v6 v7
  = du_sem'45'fuseNat_1154 v1 v2 v3 v4 v6 v7
du_sem'45'fuseNat_1154 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
du_sem'45'fuseNat_1154 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Semantics.Functor.du_fuseNatS_632
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_38 (coe v1))
      erased
      (coe
         (\ v6 v7 ->
            coe
              du_coerce'45'μ'45'in_746 (coe v0)
              (coe
                 v4 v6 (coe du_coerce'45'μ'45'out_788 (coe v1) (coe v3) (coe v7)))))
      (coe
         (\ v6 ->
            coe v5 (coe du_coerce'45'μ'45'out_788 (coe v0) (coe v2) (coe v6))))
-- Once.Semantics.Value.sem-fuseNat-cong
d_sem'45'fuseNat'45'cong_1198 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
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
d_sem'45'fuseNat'45'cong_1198 = erased
-- Once.Semantics.Value._.Φ-eq
d_Φ'45'eq_1230 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
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
d_Φ'45'eq_1230 = erased
-- Once.Semantics.Value.sem-fuseNat-events
d_sem'45'fuseNat'45'events_1250 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sem'45'fuseNat'45'events_1250 ~v0 ~v1 v2 v3 v4 v5 v6 v7 ~v8 v9
                                v10
  = du_sem'45'fuseNat'45'events_1250 v2 v3 v4 v5 v6 v7 v9 v10
du_sem'45'fuseNat'45'events_1250 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sem'45'fuseNat'45'events_1250 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Semantics.Functor.du_fuseNatW_654
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_38 (coe v2))
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_38 (coe v3))
      (coe v0) (coe v1)
      (coe
         (\ v8 v9 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
              (coe
                 du_coerce'45'μ'45'in_746 (coe v2)
                 (coe
                    v6 v8
                    (coe du_coerce'45'μ'45'out_788 (coe v3) (coe v5) (coe v9))))))
      (coe
         (\ v8 ->
            coe v7 (coe du_coerce'45'μ'45'out_788 (coe v2) (coe v4) (coe v8))))
-- Once.Semantics.Value.sem-Out-In
d_sem'45'Out'45'In_1284 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'Out'45'In_1284 = erased
-- Once.Semantics.Value.sem-In-Out
d_sem'45'In'45'Out_1296 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'In'45'Out_1296 = erased
-- Once.Semantics.Value.fmap-coerce-μ-coherence
d_fmap'45'coerce'45'μ'45'coherence_1312 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence_1312 = erased
-- Once.Semantics.Value.fmap-coerce-μ-coherence′
d_fmap'45'coerce'45'μ'45'coherence'8242'_1362 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fmap'45'coerce'45'μ'45'coherence'8242'_1362 = erased
-- Once.Semantics.Value.sem-cata-compute
d_sem'45'cata'45'compute_1410 ::
  () ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sem'45'cata'45'compute_1410 = erased
