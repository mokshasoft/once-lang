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

-- Once.Internal.Polynomial.SFunctor
d_SFunctor_6 = ()
data T_SFunctor_6
  = C_SK_8 | C_SId_10 | C__S'8853'__12 T_SFunctor_6 T_SFunctor_6 |
    C__S'8855'__14 T_SFunctor_6 T_SFunctor_6
-- Once.Internal.Polynomial.⟦_⟧SF
d_'10214'_'10215'SF_16 :: T_SFunctor_6 -> () -> ()
d_'10214'_'10215'SF_16 = erased
-- Once.Internal.Polynomial.sfmap
d_sfmap_42 ::
  T_SFunctor_6 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sfmap_42 v0 ~v1 ~v2 v3 v4 = du_sfmap_42 v0 v3 v4
du_sfmap_42 ::
  T_SFunctor_6 -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_sfmap_42 v0 v1 v2
  = case coe v0 of
      C_SK_8 -> coe v2
      C_SId_10 -> coe v1 v2
      C__S'8853'__12 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_sfmap_42 (coe v3) (coe v1) (coe v5))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_sfmap_42 (coe v4) (coe v1) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__S'8855'__14 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sfmap_42 (coe v3) (coe v1) (coe v5))
                    (coe du_sfmap_42 (coe v4) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Polynomial.μS
d_μS_82 a0 = ()
newtype T_μS_82 = C_'10216'_'10217'_86 AgdaAny
-- Once.Internal.Polynomial.outS
d_outS_90 :: T_μS_82 -> AgdaAny
d_outS_90 v0
  = case coe v0 of
      C_'10216'_'10217'_86 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Polynomial.νS
d_νS_98 a0 = ()
data T_νS_98 = C_constructor_106 MAlonzo.Code.Once.Res.T_Res_6
-- Once.Internal.Polynomial.νS.unfoldS
d_unfoldS_104 :: T_νS_98 -> MAlonzo.Code.Once.Res.T_Res_6
d_unfoldS_104 v0
  = case coe v0 of
      C_constructor_106 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Polynomial.cataS
d_cataS_112 ::
  T_SFunctor_6 -> () -> (AgdaAny -> AgdaAny) -> T_μS_82 -> AgdaAny
d_cataS_112 v0 ~v1 v2 v3 = du_cataS_112 v0 v2 v3
du_cataS_112 ::
  T_SFunctor_6 -> (AgdaAny -> AgdaAny) -> T_μS_82 -> AgdaAny
du_cataS_112 v0 v1 v2
  = case coe v2 of
      C_'10216'_'10217'_86 v3
        -> coe
             v1 (coe du_sfmapCata_120 (coe v0) (coe v0) (coe v1) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Polynomial.sfmapCata
d_sfmapCata_120 ::
  T_SFunctor_6 ->
  T_SFunctor_6 -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sfmapCata_120 v0 v1 ~v2 v3 v4 = du_sfmapCata_120 v0 v1 v3 v4
du_sfmapCata_120 ::
  T_SFunctor_6 ->
  T_SFunctor_6 -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_sfmapCata_120 v0 v1 v2 v3
  = case coe v0 of
      C_SK_8 -> coe v3
      C_SId_10 -> coe du_cataS_112 (coe v1) (coe v2) (coe v3)
      C__S'8853'__12 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_sfmapCata_120 (coe v4) (coe v1) (coe v2) (coe v6))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_sfmapCata_120 (coe v5) (coe v1) (coe v2) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__S'8855'__14 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sfmapCata_120 (coe v4) (coe v1) (coe v2) (coe v6))
                    (coe du_sfmapCata_120 (coe v5) (coe v1) (coe v2) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Polynomial.anaS
d_anaS_168 ::
  T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) -> AgdaAny -> T_νS_98
d_anaS_168 v0 ~v1 v2 v3 = du_anaS_168 v0 v2 v3
du_anaS_168 ::
  T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) -> AgdaAny -> T_νS_98
du_anaS_168 v0 v1 v2
  = coe
      C_constructor_106
      (coe du_anaLayerS_176 (coe v0) (coe v0) (coe v1) (coe v1 v2))
-- Once.Internal.Polynomial.anaLayerS
d_anaLayerS_176 ::
  T_SFunctor_6 ->
  T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Res.T_Res_6 -> MAlonzo.Code.Once.Res.T_Res_6
d_anaLayerS_176 v0 v1 ~v2 v3 v4 = du_anaLayerS_176 v0 v1 v3 v4
du_anaLayerS_176 ::
  T_SFunctor_6 ->
  T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Res.T_Res_6 -> MAlonzo.Code.Once.Res.T_Res_6
du_anaLayerS_176 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Res.C_stopped_10 -> coe v3
      MAlonzo.Code.Once.Res.C_returns_12 v4
        -> coe
             MAlonzo.Code.Once.Res.C_returns_12
             (coe du_sfmapAna_184 (coe v0) (coe v1) (coe v2) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Polynomial.sfmapAna
d_sfmapAna_184 ::
  T_SFunctor_6 ->
  T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) -> AgdaAny -> AgdaAny
d_sfmapAna_184 v0 v1 ~v2 v3 v4 = du_sfmapAna_184 v0 v1 v3 v4
du_sfmapAna_184 ::
  T_SFunctor_6 ->
  T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) -> AgdaAny -> AgdaAny
du_sfmapAna_184 v0 v1 v2 v3
  = case coe v1 of
      C_SK_8 -> coe v3
      C_SId_10 -> coe du_anaS_168 (coe v0) (coe v2) (coe v3)
      C__S'8853'__12 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_sfmapAna_184 (coe v0) (coe v4) (coe v2) (coe v6))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_sfmapAna_184 (coe v0) (coe v5) (coe v2) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__S'8855'__14 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sfmapAna_184 (coe v0) (coe v4) (coe v2) (coe v6))
                    (coe du_sfmapAna_184 (coe v0) (coe v5) (coe v2) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
