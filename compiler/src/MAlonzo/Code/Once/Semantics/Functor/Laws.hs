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

module MAlonzo.Code.Once.Semantics.Functor.Laws where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Semantics.Functor

-- Once.Semantics.Functor.Laws.⟦_⟧SF-rel
d_'10214'_'10215'SF'45'rel_16 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () -> () -> (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> AgdaAny -> ()
d_'10214'_'10215'SF'45'rel_16 = erased
-- Once.Semantics.Functor.Laws._∼S_
d__'8764'S__82 a0 a1 a2 = ()
data T__'8764'S__82 = C_constructor_94 AgdaAny
-- Once.Semantics.Functor.Laws._∼S_.unfoldS-∼
d_unfoldS'45''8764'_92 :: T__'8764'S__82 -> AgdaAny
d_unfoldS'45''8764'_92 v0
  = case coe v0 of
      C_constructor_94 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Functor.Laws.bisimS-to-eq
d_bisimS'45'to'45'eq_102
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Semantics.Functor.Laws.bisimS-to-eq"
-- Once.Semantics.Functor.Laws.sfmap-rel
d_sfmap'45'rel_124 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sfmap'45'rel_124 v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_sfmap'45'rel_124 v0 v6 v7 v8 v9
du_sfmap'45'rel_124 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sfmap'45'rel_124 v0 v1 v2 v3 v4
  = case coe v0 of
      MAlonzo.Code.Once.Semantics.Functor.C_SK_8 -> coe v4
      MAlonzo.Code.Once.Semantics.Functor.C_SId_10 -> coe v1 v2 v3 v4
      MAlonzo.Code.Once.Semantics.Functor.C__S'8853'__12 v5 v6
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
                      -> coe
                           du_sfmap'45'rel_124 (coe v5) (coe v1) (coe v7) (coe v8) (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                      -> coe
                           du_sfmap'45'rel_124 (coe v6) (coe v1) (coe v7) (coe v8) (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Semantics.Functor.C__S'8855'__14 v5 v6
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> case coe v4 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     du_sfmap'45'rel_124 (coe v5) (coe v1) (coe v7) (coe v9)
                                     (coe v11))
                                  (coe
                                     du_sfmap'45'rel_124 (coe v6) (coe v1) (coe v8) (coe v10)
                                     (coe v12))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Functor.Laws.sfmap-f-rel
d_sfmap'45'f'45'rel_196 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sfmap'45'f'45'rel_196 v0 ~v1 ~v2 ~v3 v4 v5
  = du_sfmap'45'f'45'rel_196 v0 v4 v5
du_sfmap'45'f'45'rel_196 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_sfmap'45'f'45'rel_196 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Semantics.Functor.C_SK_8 -> erased
      MAlonzo.Code.Once.Semantics.Functor.C_SId_10 -> coe v1 v2
      MAlonzo.Code.Once.Semantics.Functor.C__S'8853'__12 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe du_sfmap'45'f'45'rel_196 (coe v3) (coe v1) (coe v5)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe du_sfmap'45'f'45'rel_196 (coe v4) (coe v1) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Semantics.Functor.C__S'8855'__14 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_sfmap'45'f'45'rel_196 (coe v3) (coe v1) (coe v5))
                    (coe du_sfmap'45'f'45'rel_196 (coe v4) (coe v1) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Functor.Laws.anaS-unfoldS-bisim
d_anaS'45'unfoldS'45'bisim_236 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 -> T__'8764'S__82
d_anaS'45'unfoldS'45'bisim_236 v0 v1
  = coe
      C_constructor_94
      (coe
         d_sfmapAna'45'bisim_244 (coe v0) (coe v0)
         (coe MAlonzo.Code.Once.Semantics.Functor.d_unfoldS_204 (coe v1)))
-- Once.Semantics.Functor.Laws.sfmapAna-bisim
d_sfmapAna'45'bisim_244 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  AgdaAny -> AgdaAny
d_sfmapAna'45'bisim_244 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Semantics.Functor.C_SK_8 -> erased
      MAlonzo.Code.Once.Semantics.Functor.C_SId_10
        -> coe d_anaS'45'unfoldS'45'bisim_236 (coe v0) (coe v2)
      MAlonzo.Code.Once.Semantics.Functor.C__S'8853'__12 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe d_sfmapAna'45'bisim_244 (coe v0) (coe v3) (coe v5)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe d_sfmapAna'45'bisim_244 (coe v0) (coe v4) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Semantics.Functor.C__S'8855'__14 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_sfmapAna'45'bisim_244 (coe v0) (coe v3) (coe v5))
                    (coe d_sfmapAna'45'bisim_244 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Semantics.Functor.Laws.anaS-Out-id
d_anaS'45'Out'45'id_278 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_anaS'45'Out'45'id_278 = erased
