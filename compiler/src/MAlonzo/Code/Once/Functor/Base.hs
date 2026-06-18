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

module MAlonzo.Code.Once.Functor.Base where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base

-- Once.Functor.Base.SFunctor
d_SFunctor_6 = ()
data T_SFunctor_6
  = C_SK_8 | C_SId_10 | C__S'8853'__12 T_SFunctor_6 T_SFunctor_6 |
    C__S'8855'__14 T_SFunctor_6 T_SFunctor_6
-- Once.Functor.Base.⟦_⟧SF
d_'10214'_'10215'SF_16 :: T_SFunctor_6 -> () -> ()
d_'10214'_'10215'SF_16 = erased
-- Once.Functor.Base.sfmap
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
-- Once.Functor.Base.sfmap-id
d_sfmap'45'id_88 ::
  T_SFunctor_6 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmap'45'id_88 = erased
-- Once.Functor.Base.sfmap-comp
d_sfmap'45'comp_132 ::
  T_SFunctor_6 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmap'45'comp_132 = erased
-- Once.Functor.Base.μS
d_μS_182 a0 = ()
newtype T_μS_182 = C_'10216'_'10217'_186 AgdaAny
-- Once.Functor.Base.outS
d_outS_190 :: T_μS_182 -> AgdaAny
d_outS_190 v0
  = case coe v0 of
      C_'10216'_'10217'_186 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Base.νS
d_νS_198 a0 = ()
data T_νS_198 = C_constructor_206 AgdaAny
-- Once.Functor.Base.νS.unfoldS
d_unfoldS_204 :: T_νS_198 -> AgdaAny
d_unfoldS_204 v0
  = case coe v0 of
      C_constructor_206 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Base.cataS
d_cataS_212 ::
  T_SFunctor_6 -> () -> (AgdaAny -> AgdaAny) -> T_μS_182 -> AgdaAny
d_cataS_212 v0 ~v1 v2 v3 = du_cataS_212 v0 v2 v3
du_cataS_212 ::
  T_SFunctor_6 -> (AgdaAny -> AgdaAny) -> T_μS_182 -> AgdaAny
du_cataS_212 v0 v1 v2
  = case coe v2 of
      C_'10216'_'10217'_186 v3
        -> coe
             v1 (coe du_sfmapCata_220 (coe v0) (coe v0) (coe v1) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Base.sfmapCata
d_sfmapCata_220 ::
  T_SFunctor_6 ->
  T_SFunctor_6 -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sfmapCata_220 v0 v1 ~v2 v3 v4 = du_sfmapCata_220 v0 v1 v3 v4
du_sfmapCata_220 ::
  T_SFunctor_6 ->
  T_SFunctor_6 -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_sfmapCata_220 v0 v1 v2 v3
  = case coe v0 of
      C_SK_8 -> coe v3
      C_SId_10 -> coe du_cataS_212 (coe v1) (coe v2) (coe v3)
      C__S'8853'__12 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_sfmapCata_220 (coe v4) (coe v1) (coe v2) (coe v6))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_sfmapCata_220 (coe v5) (coe v1) (coe v2) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__S'8855'__14 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sfmapCata_220 (coe v4) (coe v1) (coe v2) (coe v6))
                    (coe du_sfmapCata_220 (coe v5) (coe v1) (coe v2) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Base.anaS
d_anaS_268 ::
  T_SFunctor_6 -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> T_νS_198
d_anaS_268 v0 ~v1 v2 v3 = du_anaS_268 v0 v2 v3
du_anaS_268 ::
  T_SFunctor_6 -> (AgdaAny -> AgdaAny) -> AgdaAny -> T_νS_198
du_anaS_268 v0 v1 v2
  = coe
      C_constructor_206
      (coe du_sfmapAna_276 (coe v0) (coe v0) (coe v1) (coe v1 v2))
-- Once.Functor.Base.sfmapAna
d_sfmapAna_276 ::
  T_SFunctor_6 ->
  T_SFunctor_6 -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sfmapAna_276 v0 v1 ~v2 v3 v4 = du_sfmapAna_276 v0 v1 v3 v4
du_sfmapAna_276 ::
  T_SFunctor_6 ->
  T_SFunctor_6 -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_sfmapAna_276 v0 v1 v2 v3
  = case coe v1 of
      C_SK_8 -> coe v3
      C_SId_10 -> coe du_anaS_268 (coe v0) (coe v2) (coe v3)
      C__S'8853'__12 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_sfmapAna_276 (coe v0) (coe v4) (coe v2) (coe v6))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_sfmapAna_276 (coe v0) (coe v5) (coe v2) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__S'8855'__14 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sfmapAna_276 (coe v0) (coe v4) (coe v2) (coe v6))
                    (coe du_sfmapAna_276 (coe v0) (coe v5) (coe v2) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Base.fold-unfoldS
d_fold'45'unfoldS_324 ::
  T_SFunctor_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fold'45'unfoldS_324 = erased
-- Once.Functor.Base.unfold-foldS
d_unfold'45'foldS_334 ::
  T_SFunctor_6 ->
  T_μS_182 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unfold'45'foldS_334 = erased
-- Once.Functor.Base.sfmapCata-is-sfmap
d_sfmapCata'45'is'45'sfmap_350 ::
  T_SFunctor_6 ->
  T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmapCata'45'is'45'sfmap_350 = erased
-- Once.Functor.Base.cataS-computation
d_cataS'45'computation_396 ::
  T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cataS'45'computation_396 = erased
-- Once.Functor.Base.cataS-In-id
d_cataS'45'In'45'id_410 ::
  T_SFunctor_6 ->
  T_μS_182 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cataS'45'In'45'id_410 = erased
-- Once.Functor.Base.sfmapCata-In-id
d_sfmapCata'45'In'45'id_418 ::
  T_SFunctor_6 ->
  T_SFunctor_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmapCata'45'In'45'id_418 = erased
-- Once.Functor.Base.cataS-cong
d_cataS'45'cong_462 ::
  T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  T_μS_182 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cataS'45'cong_462 = erased
-- Once.Functor.Base.sfmapCata-cong
d_sfmapCata'45'cong_478 ::
  T_SFunctor_6 ->
  T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmapCata'45'cong_478 = erased
-- Once.Functor.Base.sfmapAna-is-sfmap
d_sfmapAna'45'is'45'sfmap_538 ::
  T_SFunctor_6 ->
  T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmapAna'45'is'45'sfmap_538 = erased
-- Once.Functor.Base.anaS-unfold
d_anaS'45'unfold_594 ::
  T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_anaS'45'unfold_594 = erased
-- Once.Functor.Base.paraS
d_paraS_606 ::
  T_SFunctor_6 -> () -> (AgdaAny -> AgdaAny) -> T_μS_182 -> AgdaAny
d_paraS_606 v0 ~v1 v2 v3 = du_paraS_606 v0 v2 v3
du_paraS_606 ::
  T_SFunctor_6 -> (AgdaAny -> AgdaAny) -> T_μS_182 -> AgdaAny
du_paraS_606 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         du_cataS_212 (coe v0) (coe du_alg''_620 (coe v0) (coe v1))
         (coe v2))
-- Once.Functor.Base._.alg'
d_alg''_620 ::
  T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  T_μS_182 -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_alg''_620 v0 ~v1 v2 ~v3 v4 = du_alg''_620 v0 v2 v4
du_alg''_620 ::
  T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_alg''_620 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         C_'10216'_'10217'_186
         (coe
            du_sfmap_42 (coe v0)
            (coe (\ v3 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
            (coe v2)))
      (coe v1 v2)
-- Once.Functor.Base.fuseNatS
d_fuseNatS_632 ::
  T_SFunctor_6 ->
  T_SFunctor_6 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_μS_182 -> AgdaAny
d_fuseNatS_632 ~v0 v1 v2 v3 v4 = du_fuseNatS_632 v1 v2 v3 v4
du_fuseNatS_632 ::
  T_SFunctor_6 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_μS_182 -> AgdaAny
du_fuseNatS_632 v0 v1 v2 v3
  = coe du_cataS_212 (coe v0) (coe (\ v4 -> coe v3 (coe v2 v1 v4)))
-- Once.Functor.Base.fuseNatW
d_fuseNatW_654 ::
  T_SFunctor_6 ->
  T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (() -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_μS_182 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fuseNatW_654 v0 v1 ~v2 ~v3 v4 v5 v6 v7
  = du_fuseNatW_654 v0 v1 v4 v5 v6 v7
du_fuseNatW_654 ::
  T_SFunctor_6 ->
  T_SFunctor_6 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (() -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_μS_182 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fuseNatW_654 v0 v1 v2 v3 v4 v5
  = coe
      du_cataS_212 (coe v1)
      (coe du_φ_704 (coe v0) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Functor.Base._.collectM
d_collectM_678 ::
  T_SFunctor_6 ->
  T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (() -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_SFunctor_6 -> AgdaAny -> AgdaAny
d_collectM_678 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 v8 v9
  = du_collectM_678 v4 v5 v8 v9
du_collectM_678 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_SFunctor_6 -> AgdaAny -> AgdaAny
du_collectM_678 v0 v1 v2 v3
  = case coe v2 of
      C_SK_8 -> coe v1
      C_SId_10
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5 -> coe v4
             _ -> MAlonzo.RTE.mazUnreachableError
      C__S'8853'__12 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> coe du_collectM_678 (coe v0) (coe v1) (coe v4) (coe v6)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> coe du_collectM_678 (coe v0) (coe v1) (coe v5) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      C__S'8855'__14 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    v0 (coe du_collectM_678 (coe v0) (coe v1) (coe v4) (coe v6))
                    (coe du_collectM_678 (coe v0) (coe v1) (coe v5) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Base._.φ
d_φ_704 ::
  T_SFunctor_6 ->
  T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (() -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_φ_704 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 = du_φ_704 v0 v4 v5 v6 v7 v8
du_φ_704 ::
  T_SFunctor_6 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (() -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_φ_704 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         v1
         (coe
            v1 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3 erased v5))
            (coe
               du_collectM_678 (coe v1) (coe v2) (coe v0)
               (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3 erased v5))))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               v4
               (coe
                  du_sfmap_42 (coe v0)
                  (coe (\ v6 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v6)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3 erased v5))))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            v4
            (coe
               du_sfmap_42 (coe v0)
               (coe (\ v6 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v6)))
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3 erased v5)))))
-- Once.Functor.Base.NatSF
d_NatSF_714 a0 a1 = ()
data T_NatSF_714
  = C_ntId_716 | C_ntK_722 (AgdaAny -> AgdaAny) |
    C_ntFst_730 T_NatSF_714 | C_ntSnd_738 T_NatSF_714 |
    C_ntCase_746 T_NatSF_714 T_NatSF_714 | C_ntInl_754 T_NatSF_714 |
    C_ntInr_762 T_NatSF_714 | C_ntPair_770 T_NatSF_714 T_NatSF_714
-- Once.Functor.Base.appNatSF
d_appNatSF_778 ::
  T_SFunctor_6 ->
  T_SFunctor_6 -> T_NatSF_714 -> () -> AgdaAny -> AgdaAny
d_appNatSF_778 v0 v1 v2 ~v3 v4 = du_appNatSF_778 v0 v1 v2 v4
du_appNatSF_778 ::
  T_SFunctor_6 -> T_SFunctor_6 -> T_NatSF_714 -> AgdaAny -> AgdaAny
du_appNatSF_778 v0 v1 v2 v3
  = case coe v2 of
      C_ntId_716 -> coe v3
      C_ntK_722 v6 -> coe v6 v3
      C_ntFst_730 v7
        -> case coe v0 of
             C__S'8855'__14 v8 v9
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                      -> coe du_appNatSF_778 (coe v8) (coe v1) (coe v7) (coe v10)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_ntSnd_738 v7
        -> case coe v0 of
             C__S'8855'__14 v8 v9
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                      -> coe du_appNatSF_778 (coe v9) (coe v1) (coe v7) (coe v11)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_ntCase_746 v7 v8
        -> case coe v0 of
             C__S'8853'__12 v9 v10
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> coe du_appNatSF_778 (coe v9) (coe v1) (coe v7) (coe v11)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> coe du_appNatSF_778 (coe v10) (coe v1) (coe v8) (coe v11)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_ntInl_754 v7
        -> case coe v1 of
             C__S'8853'__12 v8 v9
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_appNatSF_778 (coe v0) (coe v8) (coe v7) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_ntInr_762 v7
        -> case coe v1 of
             C__S'8853'__12 v8 v9
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_appNatSF_778 (coe v0) (coe v9) (coe v7) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_ntPair_770 v7 v8
        -> case coe v1 of
             C__S'8855'__14 v9 v10
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_appNatSF_778 (coe v0) (coe v9) (coe v7) (coe v3))
                    (coe du_appNatSF_778 (coe v0) (coe v10) (coe v8) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Base.appNatSF-natural
d_appNatSF'45'natural_834 ::
  T_SFunctor_6 ->
  T_SFunctor_6 ->
  T_NatSF_714 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_appNatSF'45'natural_834 = erased
-- Once.Functor.Base.fuseNT
d_fuseNT_900 ::
  T_SFunctor_6 ->
  T_SFunctor_6 ->
  () -> T_NatSF_714 -> (AgdaAny -> AgdaAny) -> T_μS_182 -> AgdaAny
d_fuseNT_900 v0 v1 ~v2 v3 v4 = du_fuseNT_900 v0 v1 v3 v4
du_fuseNT_900 ::
  T_SFunctor_6 ->
  T_SFunctor_6 ->
  T_NatSF_714 -> (AgdaAny -> AgdaAny) -> T_μS_182 -> AgdaAny
du_fuseNT_900 v0 v1 v2 v3
  = coe
      du_fuseNatS_632 (coe v1) erased
      (\ v4 v5 -> coe du_appNatSF_778 (coe v1) (coe v0) (coe v2) v5)
      (coe v3)
-- Once.Functor.Base.fuseNTW
d_fuseNTW_920 ::
  T_SFunctor_6 ->
  T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_NatSF_714 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_μS_182 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fuseNTW_920 v0 v1 ~v2 ~v3 v4 v5 v6 v7
  = du_fuseNTW_920 v0 v1 v4 v5 v6 v7
du_fuseNTW_920 ::
  T_SFunctor_6 ->
  T_SFunctor_6 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_NatSF_714 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_μS_182 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fuseNTW_920 v0 v1 v2 v3 v4 v5
  = coe
      du_fuseNatW_654 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         (\ v6 v7 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
              (coe du_appNatSF_778 (coe v1) (coe v0) (coe v4) (coe v7))))
      (coe v5)
-- Once.Functor.Base.⟦_⟧SF-rel
d_'10214'_'10215'SF'45'rel_950 ::
  T_SFunctor_6 ->
  () -> () -> (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> AgdaAny -> ()
d_'10214'_'10215'SF'45'rel_950 = erased
-- Once.Functor.Base._∼S_
d__'8764'S__1016 a0 a1 a2 = ()
data T__'8764'S__1016 = C_constructor_1028 AgdaAny
-- Once.Functor.Base._∼S_.unfoldS-∼
d_unfoldS'45''8764'_1026 :: T__'8764'S__1016 -> AgdaAny
d_unfoldS'45''8764'_1026 v0
  = case coe v0 of
      C_constructor_1028 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Base.bisimS-to-eq
d_bisimS'45'to'45'eq_1036
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Functor.Base.bisimS-to-eq"
-- Once.Functor.Base.sfmap-rel
d_sfmap'45'rel_1058 ::
  T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sfmap'45'rel_1058 v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_sfmap'45'rel_1058 v0 v6 v7 v8 v9
du_sfmap'45'rel_1058 ::
  T_SFunctor_6 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sfmap'45'rel_1058 v0 v1 v2 v3 v4
  = case coe v0 of
      C_SK_8 -> coe v4
      C_SId_10 -> coe v1 v2 v3 v4
      C__S'8853'__12 v5 v6
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
                      -> coe
                           du_sfmap'45'rel_1058 (coe v5) (coe v1) (coe v7) (coe v8) (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                      -> coe
                           du_sfmap'45'rel_1058 (coe v6) (coe v1) (coe v7) (coe v8) (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C__S'8855'__14 v5 v6
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> case coe v4 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     du_sfmap'45'rel_1058 (coe v5) (coe v1) (coe v7) (coe v9)
                                     (coe v11))
                                  (coe
                                     du_sfmap'45'rel_1058 (coe v6) (coe v1) (coe v8) (coe v10)
                                     (coe v12))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Base.sfmap-f-rel
d_sfmap'45'f'45'rel_1130 ::
  T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sfmap'45'f'45'rel_1130 v0 ~v1 ~v2 ~v3 v4 v5
  = du_sfmap'45'f'45'rel_1130 v0 v4 v5
du_sfmap'45'f'45'rel_1130 ::
  T_SFunctor_6 -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_sfmap'45'f'45'rel_1130 v0 v1 v2
  = case coe v0 of
      C_SK_8 -> erased
      C_SId_10 -> coe v1 v2
      C__S'8853'__12 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe du_sfmap'45'f'45'rel_1130 (coe v3) (coe v1) (coe v5)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe du_sfmap'45'f'45'rel_1130 (coe v4) (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      C__S'8855'__14 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sfmap'45'f'45'rel_1130 (coe v3) (coe v1) (coe v5))
                    (coe du_sfmap'45'f'45'rel_1130 (coe v4) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Base.anaS-unfoldS-bisim
d_anaS'45'unfoldS'45'bisim_1170 ::
  T_SFunctor_6 -> T_νS_198 -> T__'8764'S__1016
d_anaS'45'unfoldS'45'bisim_1170 v0 v1
  = coe
      C_constructor_1028
      (coe
         d_sfmapAna'45'bisim_1178 (coe v0) (coe v0)
         (coe d_unfoldS_204 (coe v1)))
-- Once.Functor.Base.sfmapAna-bisim
d_sfmapAna'45'bisim_1178 ::
  T_SFunctor_6 -> T_SFunctor_6 -> AgdaAny -> AgdaAny
d_sfmapAna'45'bisim_1178 v0 v1 v2
  = case coe v1 of
      C_SK_8 -> erased
      C_SId_10 -> coe d_anaS'45'unfoldS'45'bisim_1170 (coe v0) (coe v2)
      C__S'8853'__12 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe d_sfmapAna'45'bisim_1178 (coe v0) (coe v3) (coe v5)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe d_sfmapAna'45'bisim_1178 (coe v0) (coe v4) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      C__S'8855'__14 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_sfmapAna'45'bisim_1178 (coe v0) (coe v3) (coe v5))
                    (coe d_sfmapAna'45'bisim_1178 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Base.anaS-Out-id
d_anaS'45'Out'45'id_1212 ::
  T_SFunctor_6 ->
  T_νS_198 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_anaS'45'Out'45'id_1212 = erased
