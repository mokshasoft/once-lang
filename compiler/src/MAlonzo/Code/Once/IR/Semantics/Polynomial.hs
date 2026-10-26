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

module MAlonzo.Code.Once.IR.Semantics.Polynomial where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.Spec.Polynomial

-- Once.IR.Semantics.Polynomial.outS
d_outS_10 :: MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
d_outS_10 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Polynomial.C_inS_86 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Polynomial.νS
d_νS_18 a0 = ()
data T_νS_18 = C_constructor_26 MAlonzo.Code.Once.Res.T_Res_6
-- Once.IR.Semantics.Polynomial.νS.unfoldS
d_unfoldS_24 :: T_νS_18 -> MAlonzo.Code.Once.Res.T_Res_6
d_unfoldS_24 v0
  = case coe v0 of
      C_constructor_26 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Polynomial.cataS
d_cataS_32 ::
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
d_cataS_32 v0 ~v1 v2 v3 = du_cataS_32 v0 v2 v3
du_cataS_32 ::
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
du_cataS_32 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Polynomial.C_inS_86 v3
        -> coe v1 (coe du_sfmapCata_40 (coe v0) (coe v0) (coe v1) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Polynomial.sfmapCata
d_sfmapCata_40 ::
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sfmapCata_40 v0 v1 ~v2 v3 v4 = du_sfmapCata_40 v0 v1 v3 v4
du_sfmapCata_40 ::
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_sfmapCata_40 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Polynomial.C_SK_8 -> coe v3
      MAlonzo.Code.Once.Spec.Polynomial.C_SId_10
        -> coe du_cataS_32 (coe v1) (coe v2) (coe v3)
      MAlonzo.Code.Once.Spec.Polynomial.C__S'8853'__12 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_sfmapCata_40 (coe v4) (coe v1) (coe v2) (coe v6))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_sfmapCata_40 (coe v5) (coe v1) (coe v2) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Polynomial.C__S'8855'__14 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sfmapCata_40 (coe v4) (coe v1) (coe v2) (coe v6))
                    (coe du_sfmapCata_40 (coe v5) (coe v1) (coe v2) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Polynomial.anaS
d_anaS_88 ::
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) -> AgdaAny -> T_νS_18
d_anaS_88 v0 ~v1 v2 v3 = du_anaS_88 v0 v2 v3
du_anaS_88 ::
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) -> AgdaAny -> T_νS_18
du_anaS_88 v0 v1 v2
  = coe
      C_constructor_26
      (coe du_anaLayerS_96 (coe v0) (coe v0) (coe v1) (coe v1 v2))
-- Once.IR.Semantics.Polynomial.anaLayerS
d_anaLayerS_96 ::
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Res.T_Res_6 -> MAlonzo.Code.Once.Res.T_Res_6
d_anaLayerS_96 v0 v1 ~v2 v3 v4 = du_anaLayerS_96 v0 v1 v3 v4
du_anaLayerS_96 ::
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Res.T_Res_6 -> MAlonzo.Code.Once.Res.T_Res_6
du_anaLayerS_96 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Res.C_stopped_10 -> coe v3
      MAlonzo.Code.Once.Res.C_returns_12 v4
        -> coe
             MAlonzo.Code.Once.Res.C_returns_12
             (coe du_sfmapAna_104 (coe v0) (coe v1) (coe v2) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Polynomial.sfmapAna
d_sfmapAna_104 ::
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) -> AgdaAny -> AgdaAny
d_sfmapAna_104 v0 v1 ~v2 v3 v4 = du_sfmapAna_104 v0 v1 v3 v4
du_sfmapAna_104 ::
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) -> AgdaAny -> AgdaAny
du_sfmapAna_104 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Polynomial.C_SK_8 -> coe v3
      MAlonzo.Code.Once.Spec.Polynomial.C_SId_10
        -> coe du_anaS_88 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.Spec.Polynomial.C__S'8853'__12 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_sfmapAna_104 (coe v0) (coe v4) (coe v2) (coe v6))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_sfmapAna_104 (coe v0) (coe v5) (coe v2) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Polynomial.C__S'8855'__14 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sfmapAna_104 (coe v0) (coe v4) (coe v2) (coe v6))
                    (coe du_sfmapAna_104 (coe v0) (coe v5) (coe v2) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
