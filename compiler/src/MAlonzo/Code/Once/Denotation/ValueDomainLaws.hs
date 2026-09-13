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

module MAlonzo.Code.Once.Denotation.ValueDomainLaws where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Semantics.Functor

-- Once.Denotation.ValueDomainLaws._∼ᵈ_
d__'8764''7496'__12 a0 a1 a2 = ()
data T__'8764''7496'__12 = C_constructor_36 (Integer -> AgdaAny)
-- Once.Denotation.ValueDomainLaws._∼ᵈ_.traceᵈ-∼
d_trace'7496''45''8764'_30 ::
  T__'8764''7496'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trace'7496''45''8764'_30 = erased
-- Once.Denotation.ValueDomainLaws._∼ᵈ_.layerᵈ-∼
d_layer'7496''45''8764'_34 ::
  T__'8764''7496'__12 -> Integer -> AgdaAny
d_layer'7496''45''8764'_34 v0
  = case coe v0 of
      C_constructor_36 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueDomainLaws.bisimᵈ-to-eq
d_bisim'7496''45'to'45'eq_44
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Denotation.ValueDomainLaws.bisim\7496-to-eq"
-- Once.Denotation.ValueDomainLaws.CoalgRel
d_CoalgRel_54 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  ()
d_CoalgRel_54 = erased
-- Once.Denotation.ValueDomainLaws.anaᵈ-∼
d_ana'7496''45''8764'_88 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> AgdaAny -> AgdaAny -> T__'8764''7496'__12
d_ana'7496''45''8764'_88 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_ana'7496''45''8764'_88 v0 v4 v5 v6 v7 v8 v9
du_ana'7496''45''8764'_88 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> AgdaAny -> AgdaAny -> T__'8764''7496'__12
du_ana'7496''45''8764'_88 v0 v1 v2 v3 v4 v5 v6
  = coe
      C_constructor_36
      (\ v7 ->
         coe
           du_mapAna'7496''45''8764'_108 (coe v0) (coe v0) (coe v1) (coe v2)
           (coe v3)
           (coe
              MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_72 (coe v1 v4)
              (coe v7))
           (coe
              MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_72 (coe v2 v5)
              (coe v7))
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3 v4 v5 v6) v7))
-- Once.Denotation.ValueDomainLaws.mapAnaᵈ-∼
d_mapAna'7496''45''8764'_108 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mapAna'7496''45''8764'_108 v0 v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10
  = du_mapAna'7496''45''8764'_108 v0 v1 v5 v6 v7 v8 v9 v10
du_mapAna'7496''45''8764'_108 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_mapAna'7496''45''8764'_108 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v1 of
      MAlonzo.Code.Once.Semantics.Functor.C_SK_8 -> coe v7
      MAlonzo.Code.Once.Semantics.Functor.C_SId_10
        -> coe
             du_ana'7496''45''8764'_88 (coe v0) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7)
      MAlonzo.Code.Once.Semantics.Functor.C__S'8853'__12 v8 v9
        -> case coe v5 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
               -> case coe v6 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> coe
                           du_mapAna'7496''45''8764'_108 (coe v0) (coe v8) (coe v2) (coe v3)
                           (coe v4) (coe v10) (coe v11) (coe v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
               -> case coe v6 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> coe
                           du_mapAna'7496''45''8764'_108 (coe v0) (coe v9) (coe v2) (coe v3)
                           (coe v4) (coe v10) (coe v11) (coe v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Semantics.Functor.C__S'8855'__14 v8 v9
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                      -> case coe v7 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     du_mapAna'7496''45''8764'_108 (coe v0) (coe v8) (coe v2)
                                     (coe v3) (coe v4) (coe v10) (coe v12) (coe v14))
                                  (coe
                                     du_mapAna'7496''45''8764'_108 (coe v0) (coe v9) (coe v2)
                                     (coe v3) (coe v4) (coe v11) (coe v13) (coe v15))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueDomainLaws.anaᵈ-rel-eq
d_ana'7496''45'rel'45'eq_206 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ana'7496''45'rel'45'eq_206 = erased
