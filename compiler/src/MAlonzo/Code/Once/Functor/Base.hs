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
-- Once.Functor.Base._.cong₂
d_cong'8322'_136 ::
  T_SFunctor_6 ->
  T_SFunctor_6 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong'8322'_136 = erased
-- Once.Functor.Base.sfmap-comp
d_sfmap'45'comp_156 ::
  T_SFunctor_6 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmap'45'comp_156 = erased
-- Once.Functor.Base._.cong₂
d_cong'8322'_224 ::
  T_SFunctor_6 ->
  T_SFunctor_6 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong'8322'_224 = erased
-- Once.Functor.Base.μS
d_μS_230 a0 = ()
newtype T_μS_230 = C_'10216'_'10217'_234 AgdaAny
-- Once.Functor.Base.outS
d_outS_238 :: T_μS_230 -> AgdaAny
d_outS_238 v0
  = case coe v0 of
      C_'10216'_'10217'_234 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Base.νS
d_νS_246 a0 = ()
data T_νS_246 = C_constructor_254 AgdaAny
-- Once.Functor.Base.νS.unfoldS
d_unfoldS_252 :: T_νS_246 -> AgdaAny
d_unfoldS_252 v0
  = case coe v0 of
      C_constructor_254 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Base.cataS
d_cataS_260 ::
  T_SFunctor_6 -> () -> (AgdaAny -> AgdaAny) -> T_μS_230 -> AgdaAny
d_cataS_260 v0 ~v1 v2 v3 = du_cataS_260 v0 v2 v3
du_cataS_260 ::
  T_SFunctor_6 -> (AgdaAny -> AgdaAny) -> T_μS_230 -> AgdaAny
du_cataS_260 v0 v1 v2
  = case coe v2 of
      C_'10216'_'10217'_234 v3
        -> coe
             v1 (coe du_sfmapCata_268 (coe v0) (coe v0) (coe v1) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Base.sfmapCata
d_sfmapCata_268 ::
  T_SFunctor_6 ->
  T_SFunctor_6 -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sfmapCata_268 v0 v1 ~v2 v3 v4 = du_sfmapCata_268 v0 v1 v3 v4
du_sfmapCata_268 ::
  T_SFunctor_6 ->
  T_SFunctor_6 -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_sfmapCata_268 v0 v1 v2 v3
  = case coe v0 of
      C_SK_8 -> coe v3
      C_SId_10 -> coe du_cataS_260 (coe v1) (coe v2) (coe v3)
      C__S'8853'__12 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_sfmapCata_268 (coe v4) (coe v1) (coe v2) (coe v6))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_sfmapCata_268 (coe v5) (coe v1) (coe v2) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__S'8855'__14 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sfmapCata_268 (coe v4) (coe v1) (coe v2) (coe v6))
                    (coe du_sfmapCata_268 (coe v5) (coe v1) (coe v2) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Base.anaS
d_anaS_316 ::
  T_SFunctor_6 -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> T_νS_246
d_anaS_316 v0 ~v1 v2 v3 = du_anaS_316 v0 v2 v3
du_anaS_316 ::
  T_SFunctor_6 -> (AgdaAny -> AgdaAny) -> AgdaAny -> T_νS_246
du_anaS_316 v0 v1 v2
  = coe
      C_constructor_254
      (coe
         du_sfmap_42 (coe v0) (coe du_anaS_316 (coe v0) (coe v1))
         (coe v1 v2))
-- Once.Functor.Base.fold-unfoldS
d_fold'45'unfoldS_328 ::
  T_SFunctor_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fold'45'unfoldS_328 = erased
-- Once.Functor.Base.unfold-foldS
d_unfold'45'foldS_338 ::
  T_SFunctor_6 ->
  T_μS_230 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unfold'45'foldS_338 = erased
-- Once.Functor.Base.sfmapCata-is-sfmap
d_sfmapCata'45'is'45'sfmap_354 ::
  T_SFunctor_6 ->
  T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmapCata'45'is'45'sfmap_354 = erased
-- Once.Functor.Base._.cong₂
d_cong'8322'_412 ::
  T_SFunctor_6 ->
  T_SFunctor_6 ->
  T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong'8322'_412 = erased
-- Once.Functor.Base.cataS-computation
d_cataS'45'computation_424 ::
  T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cataS'45'computation_424 = erased
-- Once.Functor.Base.cataS-In-id
d_cataS'45'In'45'id_438 ::
  T_SFunctor_6 ->
  T_μS_230 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cataS'45'In'45'id_438 = erased
-- Once.Functor.Base.sfmapCata-In-id
d_sfmapCata'45'In'45'id_446 ::
  T_SFunctor_6 ->
  T_SFunctor_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sfmapCata'45'In'45'id_446 = erased
-- Once.Functor.Base._.cong₂
d_cong'8322'_498 ::
  T_SFunctor_6 ->
  T_SFunctor_6 ->
  T_SFunctor_6 ->
  AgdaAny ->
  AgdaAny ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong'8322'_498 = erased
-- Once.Functor.Base.anaS-unfold
d_anaS'45'unfold_510 ::
  T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_anaS'45'unfold_510 = erased
-- Once.Functor.Base.paraS
d_paraS_522 ::
  T_SFunctor_6 -> () -> (AgdaAny -> AgdaAny) -> T_μS_230 -> AgdaAny
d_paraS_522 v0 ~v1 v2 v3 = du_paraS_522 v0 v2 v3
du_paraS_522 ::
  T_SFunctor_6 -> (AgdaAny -> AgdaAny) -> T_μS_230 -> AgdaAny
du_paraS_522 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         du_cataS_260 (coe v0) (coe du_alg''_536 (coe v0) (coe v1))
         (coe v2))
-- Once.Functor.Base._.alg'
d_alg''_536 ::
  T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  T_μS_230 -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_alg''_536 v0 ~v1 v2 ~v3 v4 = du_alg''_536 v0 v2 v4
du_alg''_536 ::
  T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_alg''_536 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         C_'10216'_'10217'_234
         (coe
            du_sfmap_42 (coe v0)
            (coe (\ v3 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
            (coe v2)))
      (coe v1 v2)
-- Once.Functor.Base.fuseNatS
d_fuseNatS_548 ::
  T_SFunctor_6 ->
  T_SFunctor_6 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_μS_230 -> AgdaAny
d_fuseNatS_548 ~v0 v1 v2 v3 v4 = du_fuseNatS_548 v1 v2 v3 v4
du_fuseNatS_548 ::
  T_SFunctor_6 ->
  () ->
  (() -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_μS_230 -> AgdaAny
du_fuseNatS_548 v0 v1 v2 v3
  = coe du_cataS_260 (coe v0) (coe (\ v4 -> coe v3 (coe v2 v1 v4)))
-- Once.Functor.Base.fuseS
d_fuseS_566 ::
  T_SFunctor_6 ->
  T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> T_μS_230 -> AgdaAny
d_fuseS_566 v0 v1 ~v2 v3 v4 v5 = du_fuseS_566 v0 v1 v3 v4 v5
du_fuseS_566 ::
  T_SFunctor_6 ->
  T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> T_μS_230 -> AgdaAny
du_fuseS_566 v0 v1 v2 v3 v4
  = case coe v4 of
      C_'10216'_'10217'_234 v5
        -> coe
             v2
             (coe
                du_sfmapFuse_586 (coe v0) (coe v1) (coe v2) (coe v3) (coe v0)
                (coe v3 v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Base._.sfmapFuse
d_sfmapFuse_586 ::
  T_SFunctor_6 ->
  T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_SFunctor_6 -> AgdaAny -> AgdaAny
d_sfmapFuse_586 v0 v1 ~v2 v3 v4 ~v5 v6 v7
  = du_sfmapFuse_586 v0 v1 v3 v4 v6 v7
du_sfmapFuse_586 ::
  T_SFunctor_6 ->
  T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_SFunctor_6 -> AgdaAny -> AgdaAny
du_sfmapFuse_586 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      C_SK_8 -> coe v5
      C_SId_10
        -> coe du_fuseS_566 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
      C__S'8853'__12 v6 v7
        -> case coe v5 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe
                       du_sfmapFuse_586 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6)
                       (coe v8))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe
                       du_sfmapFuse_586 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7)
                       (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__S'8855'__14 v6 v7
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe
                       du_sfmapFuse_586 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6)
                       (coe v8))
                    (coe
                       du_sfmapFuse_586 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7)
                       (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Base.⟦_⟧SF-rel
d_'10214'_'10215'SF'45'rel_622 ::
  T_SFunctor_6 ->
  () -> () -> (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> AgdaAny -> ()
d_'10214'_'10215'SF'45'rel_622 = erased
-- Once.Functor.Base._∼S_
d__'8764'S__688 a0 a1 a2 = ()
data T__'8764'S__688 = C_constructor_700 AgdaAny
-- Once.Functor.Base._∼S_.unfoldS-∼
d_unfoldS'45''8764'_698 :: T__'8764'S__688 -> AgdaAny
d_unfoldS'45''8764'_698 v0
  = case coe v0 of
      C_constructor_700 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Base.bisimS-to-eq
d_bisimS'45'to'45'eq_708
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Functor.Base.bisimS-to-eq"
-- Once.Functor.Base.sfmap-rel
d_sfmap'45'rel_730 ::
  T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sfmap'45'rel_730 v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_sfmap'45'rel_730 v0 v6 v7 v8 v9
du_sfmap'45'rel_730 ::
  T_SFunctor_6 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sfmap'45'rel_730 v0 v1 v2 v3 v4
  = case coe v0 of
      C_SK_8 -> coe v4
      C_SId_10 -> coe v1 v2 v3 v4
      C__S'8853'__12 v5 v6
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
                      -> coe
                           du_sfmap'45'rel_730 (coe v5) (coe v1) (coe v7) (coe v8) (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                      -> coe
                           du_sfmap'45'rel_730 (coe v6) (coe v1) (coe v7) (coe v8) (coe v4)
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
                                     du_sfmap'45'rel_730 (coe v5) (coe v1) (coe v7) (coe v9)
                                     (coe v11))
                                  (coe
                                     du_sfmap'45'rel_730 (coe v6) (coe v1) (coe v8) (coe v10)
                                     (coe v12))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Base.sfmap-f-rel
d_sfmap'45'f'45'rel_802 ::
  T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sfmap'45'f'45'rel_802 v0 ~v1 ~v2 ~v3 v4 v5
  = du_sfmap'45'f'45'rel_802 v0 v4 v5
du_sfmap'45'f'45'rel_802 ::
  T_SFunctor_6 -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_sfmap'45'f'45'rel_802 v0 v1 v2
  = case coe v0 of
      C_SK_8 -> erased
      C_SId_10 -> coe v1 v2
      C__S'8853'__12 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe du_sfmap'45'f'45'rel_802 (coe v3) (coe v1) (coe v5)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe du_sfmap'45'f'45'rel_802 (coe v4) (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      C__S'8855'__14 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sfmap'45'f'45'rel_802 (coe v3) (coe v1) (coe v5))
                    (coe du_sfmap'45'f'45'rel_802 (coe v4) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Functor.Base.anaS-unfoldS-bisim
d_anaS'45'unfoldS'45'bisim_842 ::
  T_SFunctor_6 -> T_νS_246 -> T__'8764'S__688
d_anaS'45'unfoldS'45'bisim_842 v0 v1
  = coe
      C_constructor_700
      (coe
         du_sfmap'45'f'45'rel_802 (coe v0)
         (coe d_anaS'45'unfoldS'45'bisim_842 (coe v0))
         (coe d_unfoldS_252 (coe v1)))
-- Once.Functor.Base.anaS-Out-id
d_anaS'45'Out'45'id_852 ::
  T_SFunctor_6 ->
  T_νS_246 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_anaS'45'Out'45'id_852 = erased
