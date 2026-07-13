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

module MAlonzo.Code.Once.Adequacy.CataRel where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Semantics.Functor

-- Once.Adequacy.CataRel.RelSF
d_RelSF_14 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () -> () -> (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> AgdaAny -> ()
d_RelSF_14 = erased
-- Once.Adequacy.CataRel.cataS-rel
d_cataS'45'rel_94 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
d_cataS'45'rel_94 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_cataS'45'rel_94 v0 v4 v5 v6 v7
du_cataS'45'rel_94 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 -> AgdaAny
du_cataS'45'rel_94 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Semantics.Functor.C_'10216'_'10217'_186 v5
        -> coe
             v3
             (coe
                MAlonzo.Code.Once.Semantics.Functor.du_sfmapCata_220 (coe v0)
                (coe v0) (coe v1) (coe v5))
             (coe
                MAlonzo.Code.Once.Semantics.Functor.du_sfmapCata_220 (coe v0)
                (coe v0) (coe v2) (coe v5))
             (coe
                du_sfmapCata'45'rel_116 (coe v0) (coe v0) (coe v1) (coe v2)
                (coe v3) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CataRel.sfmapCata-rel
d_sfmapCata'45'rel_116 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sfmapCata'45'rel_116 v0 v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
  = du_sfmapCata'45'rel_116 v0 v1 v5 v6 v7 v8
du_sfmapCata'45'rel_116 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_sfmapCata'45'rel_116 v0 v1 v2 v3 v4 v5
  = case coe v0 of
      MAlonzo.Code.Once.Semantics.Functor.C_SK_8 -> erased
      MAlonzo.Code.Once.Semantics.Functor.C_SId_10
        -> coe
             du_cataS'45'rel_94 (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
      MAlonzo.Code.Once.Semantics.Functor.C__S'8853'__12 v6 v7
        -> case coe v5 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
               -> coe
                    du_sfmapCata'45'rel_116 (coe v6) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v8)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
               -> coe
                    du_sfmapCata'45'rel_116 (coe v7) (coe v1) (coe v2) (coe v3)
                    (coe v4) (coe v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Semantics.Functor.C__S'8855'__14 v6 v7
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_sfmapCata'45'rel_116 (coe v6) (coe v1) (coe v2) (coe v3)
                       (coe v4) (coe v8))
                    (coe
                       du_sfmapCata'45'rel_116 (coe v7) (coe v1) (coe v2) (coe v3)
                       (coe v4) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
