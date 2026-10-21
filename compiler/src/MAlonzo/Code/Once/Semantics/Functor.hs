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

module MAlonzo.Code.Once.Semantics.Functor where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Internal.Polynomial
import qualified MAlonzo.Code.Once.Internal.Res

-- Once.Semantics.Functor.sfmap-id
d_sfmap'45'id_14 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmap'45'id_14 = erased
-- Once.Semantics.Functor.sfmap-comp
d_sfmap'45'comp_58 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmap'45'comp_58 = erased
-- Once.Semantics.Functor.fold-unfoldS
d_fold'45'unfoldS_110 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fold'45'unfoldS_110 = erased
-- Once.Semantics.Functor.unfold-foldS
d_unfold'45'foldS_120 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unfold'45'foldS_120 = erased
-- Once.Semantics.Functor.sfmapCata-is-sfmap
d_sfmapCata'45'is'45'sfmap_136 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmapCata'45'is'45'sfmap_136 = erased
-- Once.Semantics.Functor.cataS-computation
d_cataS'45'computation_182 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cataS'45'computation_182 = erased
-- Once.Semantics.Functor.cataS-In-id
d_cataS'45'In'45'id_196 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cataS'45'In'45'id_196 = erased
-- Once.Semantics.Functor.sfmapCata-In-id
d_sfmapCata'45'In'45'id_204 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmapCata'45'In'45'id_204 = erased
-- Once.Semantics.Functor.cataS-cong
d_cataS'45'cong_248 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cataS'45'cong_248 = erased
-- Once.Semantics.Functor.sfmapCata-cong
d_sfmapCata'45'cong_264 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmapCata'45'cong_264 = erased
-- Once.Semantics.Functor.sfmapAna-is-sfmap
d_sfmapAna'45'is'45'sfmap_324 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Res.T_Res_8) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmapAna'45'is'45'sfmap_324 = erased
-- Once.Semantics.Functor.anaS-unfold
d_anaS'45'unfold_380 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Res.T_Res_8) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_anaS'45'unfold_380 = erased
-- Once.Semantics.Functor.paraS
d_paraS_410 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 -> AgdaAny
d_paraS_410 v0 ~v1 v2 v3 = du_paraS_410 v0 v2 v3
du_paraS_410 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 -> AgdaAny
du_paraS_410 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         MAlonzo.Code.Once.Internal.Polynomial.du_cataS_112 (coe v0)
         (coe du_alg''_424 (coe v0) (coe v1)) (coe v2))
-- Once.Semantics.Functor._.alg'
d_alg''_424 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_alg''_424 v0 ~v1 v2 ~v3 v4 = du_alg''_424 v0 v2 v4
du_alg''_424 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_alg''_424 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Internal.Polynomial.C_'10216'_'10217'_86
         (coe
            MAlonzo.Code.Once.Internal.Polynomial.du_sfmap_42 (coe v0)
            (coe (\ v3 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
            (coe v2)))
      (coe v1 v2)
-- Once.Semantics.Functor.fuseNatS
d_fuseNatS_436 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 -> AgdaAny
d_fuseNatS_436 ~v0 v1 v2 v3 v4 = du_fuseNatS_436 v1 v2 v3 v4
du_fuseNatS_436 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 -> AgdaAny
du_fuseNatS_436 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Internal.Polynomial.du_cataS_112 (coe v0)
      (coe (\ v4 -> coe v3 (coe v2 v1 v4)))
-- Once.Semantics.Functor.fuseNatW
d_fuseNatW_458 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (() -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fuseNatW_458 v0 v1 ~v2 ~v3 v4 v5 v6 v7
  = du_fuseNatW_458 v0 v1 v4 v5 v6 v7
du_fuseNatW_458 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (() -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fuseNatW_458 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Internal.Polynomial.du_cataS_112 (coe v1)
      (coe du_φ_508 (coe v0) (coe v2) (coe v3) (coe v4) (coe v5))
-- Once.Semantics.Functor._.collectM
d_collectM_482 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (() -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny
d_collectM_482 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 v8 v9
  = du_collectM_482 v4 v5 v8 v9
du_collectM_482 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny
du_collectM_482 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Internal.Polynomial.C_SK_8 -> coe v1
      MAlonzo.Code.Once.Internal.Polynomial.C_SId_10
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5 -> coe v4
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Polynomial.C__S'8853'__12 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> coe du_collectM_482 (coe v0) (coe v1) (coe v4) (coe v6)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> coe du_collectM_482 (coe v0) (coe v1) (coe v5) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Polynomial.C__S'8855'__14 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    v0 (coe du_collectM_482 (coe v0) (coe v1) (coe v4) (coe v6))
                    (coe du_collectM_482 (coe v0) (coe v1) (coe v5) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Functor._.φ
d_φ_508 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (() -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_φ_508 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 = du_φ_508 v0 v4 v5 v6 v7 v8
du_φ_508 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (() -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_φ_508 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         v1
         (coe
            v1 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3 erased v5))
            (coe
               du_collectM_482 (coe v1) (coe v2) (coe v0)
               (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3 erased v5))))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               v4
               (coe
                  MAlonzo.Code.Once.Internal.Polynomial.du_sfmap_42 (coe v0)
                  (coe (\ v6 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v6)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3 erased v5))))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            v4
            (coe
               MAlonzo.Code.Once.Internal.Polynomial.du_sfmap_42 (coe v0)
               (coe (\ v6 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v6)))
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3 erased v5)))))
-- Once.Semantics.Functor.NatSF
d_NatSF_518 a0 a1 = ()
data T_NatSF_518
  = C_ntId_520 | C_ntK_526 (AgdaAny -> AgdaAny) |
    C_ntFst_534 T_NatSF_518 | C_ntSnd_542 T_NatSF_518 |
    C_ntCase_550 T_NatSF_518 T_NatSF_518 | C_ntInl_558 T_NatSF_518 |
    C_ntInr_566 T_NatSF_518 | C_ntPair_574 T_NatSF_518 T_NatSF_518
-- Once.Semantics.Functor.appNatSF
d_appNatSF_582 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  T_NatSF_518 -> () -> AgdaAny -> AgdaAny
d_appNatSF_582 v0 v1 v2 ~v3 v4 = du_appNatSF_582 v0 v1 v2 v4
du_appNatSF_582 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  T_NatSF_518 -> AgdaAny -> AgdaAny
du_appNatSF_582 v0 v1 v2 v3
  = case coe v2 of
      C_ntId_520 -> coe v3
      C_ntK_526 v6 -> coe v6 v3
      C_ntFst_534 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Polynomial.C__S'8855'__14 v8 v9
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                      -> coe du_appNatSF_582 (coe v8) (coe v1) (coe v7) (coe v10)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_ntSnd_542 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Polynomial.C__S'8855'__14 v8 v9
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                      -> coe du_appNatSF_582 (coe v9) (coe v1) (coe v7) (coe v11)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_ntCase_550 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Polynomial.C__S'8853'__12 v9 v10
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> coe du_appNatSF_582 (coe v9) (coe v1) (coe v7) (coe v11)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> coe du_appNatSF_582 (coe v10) (coe v1) (coe v8) (coe v11)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_ntInl_558 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Polynomial.C__S'8853'__12 v8 v9
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_appNatSF_582 (coe v0) (coe v8) (coe v7) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_ntInr_566 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Polynomial.C__S'8853'__12 v8 v9
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_appNatSF_582 (coe v0) (coe v9) (coe v7) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_ntPair_574 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Polynomial.C__S'8855'__14 v9 v10
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_appNatSF_582 (coe v0) (coe v9) (coe v7) (coe v3))
                    (coe du_appNatSF_582 (coe v0) (coe v10) (coe v8) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Functor.appNatSF-natural
d_appNatSF'45'natural_638 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  T_NatSF_518 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_appNatSF'45'natural_638 = erased
-- Once.Semantics.Functor.fuseNT
d_fuseNT_704 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  T_NatSF_518 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 -> AgdaAny
d_fuseNT_704 v0 v1 ~v2 v3 v4 = du_fuseNT_704 v0 v1 v3 v4
du_fuseNT_704 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  T_NatSF_518 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 -> AgdaAny
du_fuseNT_704 v0 v1 v2 v3
  = coe
      du_fuseNatS_436 (coe v1) erased
      (\ v4 v5 -> coe du_appNatSF_582 (coe v1) (coe v0) (coe v2) v5)
      (coe v3)
-- Once.Semantics.Functor.fuseNTW
d_fuseNTW_724 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_NatSF_518 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_fuseNTW_724 v0 v1 ~v2 ~v3 v4 v5 v6 v7
  = du_fuseNTW_724 v0 v1 v4 v5 v6 v7
du_fuseNTW_724 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_NatSF_518 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_fuseNTW_724 v0 v1 v2 v3 v4 v5
  = coe
      du_fuseNatW_458 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe
         (\ v6 v7 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
              (coe du_appNatSF_582 (coe v1) (coe v0) (coe v4) (coe v7))))
      (coe v5)
