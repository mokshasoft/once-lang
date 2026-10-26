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

module MAlonzo.Code.Once.Internal.Polynomial where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.Spec.Polynomial

-- Once.Internal.Polynomial.outS
d_outS_8 :: MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
d_outS_8 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Polynomial.C_inS_86 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Polynomial.νS
d_νS_16 a0 = ()
data T_νS_16 = C_constructor_24 MAlonzo.Code.Once.Res.T_Res_6
-- Once.Internal.Polynomial.νS.unfoldS
d_unfoldS_22 :: T_νS_16 -> MAlonzo.Code.Once.Res.T_Res_6
d_unfoldS_22 v0
  = case coe v0 of
      C_constructor_24 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Polynomial.cataS
d_cataS_30 ::
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
d_cataS_30 v0 ~v1 v2 v3 = du_cataS_30 v0 v2 v3
du_cataS_30 ::
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
du_cataS_30 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Polynomial.C_inS_86 v3
        -> coe v1 (coe du_sfmapCata_38 (coe v0) (coe v0) (coe v1) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Polynomial.sfmapCata
d_sfmapCata_38 ::
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sfmapCata_38 v0 v1 ~v2 v3 v4 = du_sfmapCata_38 v0 v1 v3 v4
du_sfmapCata_38 ::
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_sfmapCata_38 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Polynomial.C_SK_8 -> coe v3
      MAlonzo.Code.Once.Spec.Polynomial.C_SId_10
        -> coe du_cataS_30 (coe v1) (coe v2) (coe v3)
      MAlonzo.Code.Once.Spec.Polynomial.C__S'8853'__12 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_sfmapCata_38 (coe v4) (coe v1) (coe v2) (coe v6))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_sfmapCata_38 (coe v5) (coe v1) (coe v2) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Polynomial.C__S'8855'__14 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sfmapCata_38 (coe v4) (coe v1) (coe v2) (coe v6))
                    (coe du_sfmapCata_38 (coe v5) (coe v1) (coe v2) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Polynomial.anaS
d_anaS_86 ::
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) -> AgdaAny -> T_νS_16
d_anaS_86 v0 ~v1 v2 v3 = du_anaS_86 v0 v2 v3
du_anaS_86 ::
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) -> AgdaAny -> T_νS_16
du_anaS_86 v0 v1 v2
  = coe
      C_constructor_24
      (coe du_anaLayerS_94 (coe v0) (coe v0) (coe v1) (coe v1 v2))
-- Once.Internal.Polynomial.anaLayerS
d_anaLayerS_94 ::
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Res.T_Res_6 -> MAlonzo.Code.Once.Res.T_Res_6
d_anaLayerS_94 v0 v1 ~v2 v3 v4 = du_anaLayerS_94 v0 v1 v3 v4
du_anaLayerS_94 ::
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Res.T_Res_6 -> MAlonzo.Code.Once.Res.T_Res_6
du_anaLayerS_94 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Res.C_stopped_10 -> coe v3
      MAlonzo.Code.Once.Res.C_returns_12 v4
        -> coe
             MAlonzo.Code.Once.Res.C_returns_12
             (coe du_sfmapAna_102 (coe v0) (coe v1) (coe v2) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Polynomial.sfmapAna
d_sfmapAna_102 ::
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) -> AgdaAny -> AgdaAny
d_sfmapAna_102 v0 v1 ~v2 v3 v4 = du_sfmapAna_102 v0 v1 v3 v4
du_sfmapAna_102 ::
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) -> AgdaAny -> AgdaAny
du_sfmapAna_102 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Polynomial.C_SK_8 -> coe v3
      MAlonzo.Code.Once.Spec.Polynomial.C_SId_10
        -> coe du_anaS_86 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.Spec.Polynomial.C__S'8853'__12 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_sfmapAna_102 (coe v0) (coe v4) (coe v2) (coe v6))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_sfmapAna_102 (coe v0) (coe v5) (coe v2) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Polynomial.C__S'8855'__14 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sfmapAna_102 (coe v0) (coe v4) (coe v2) (coe v6))
                    (coe du_sfmapAna_102 (coe v0) (coe v5) (coe v2) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
