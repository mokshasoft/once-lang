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
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Semantics.Functor

-- Once.Denotation.ValueDomainLaws._∼ᵈ_
d__'8764''7496'__12 a0 a1 a2 = ()
data T__'8764''7496'__12
  = C_constructor_24 MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
-- Once.Denotation.ValueDomainLaws._∼ᵈ_.force-∼
d_force'45''8764'_22 ::
  T__'8764''7496'__12 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_force'45''8764'_22 v0
  = case coe v0 of
      C_constructor_24 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueDomainLaws.∼ᵈ-refl
d_'8764''7496''45'refl_30 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Denotation.ValueDomain.T_ν'7496'_8 ->
  T__'8764''7496'__12
d_'8764''7496''45'refl_30 v0 v1
  = coe
      C_constructor_24
      (coe
         d_tree'45'refl_38 (coe v0) (coe v0)
         (coe
            MAlonzo.Code.Once.Denotation.ValueDomain.d_force'7496'_14
            (coe v1)))
-- Once.Denotation.ValueDomainLaws.tree-refl
d_tree'45'refl_38 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_tree'45'refl_38 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Denotation.TraceMonad.C_ret_182 v3
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.C_rel'45'ret_678
             (d_SF'45'rel'45'refl_46 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Denotation.TraceMonad.C_call_186 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.C_rel'45'call_690
             (\ v6 -> d_tree'45'refl_38 (coe v0) (coe v1) (coe v5 v6))
      MAlonzo.Code.Once.Denotation.TraceMonad.C_halt_190 v3 v4
        -> coe MAlonzo.Code.Once.Denotation.TraceMonad.C_rel'45'halt_696
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueDomainLaws.SF-rel-refl
d_SF'45'rel'45'refl_46 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  AgdaAny -> AgdaAny
d_SF'45'rel'45'refl_46 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Semantics.Functor.C_SK_8 -> erased
      MAlonzo.Code.Once.Semantics.Functor.C_SId_10
        -> coe d_'8764''7496''45'refl_30 (coe v0) (coe v2)
      MAlonzo.Code.Once.Semantics.Functor.C__S'8853'__12 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe d_SF'45'rel'45'refl_46 (coe v0) (coe v3) (coe v5)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe d_SF'45'rel'45'refl_46 (coe v0) (coe v4) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Semantics.Functor.C__S'8855'__14 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_SF'45'rel'45'refl_46 (coe v0) (coe v3) (coe v5))
                    (coe d_SF'45'rel'45'refl_46 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueDomainLaws.CoalgRel
d_CoalgRel_122 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) -> ()
d_CoalgRel_122 = erased
-- Once.Denotation.ValueDomainLaws.anaᵈ-∼
d_ana'7496''45''8764'_152 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666) ->
  AgdaAny -> AgdaAny -> AgdaAny -> T__'8764''7496'__12
d_ana'7496''45''8764'_152 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_ana'7496''45''8764'_152 v0 v4 v5 v6 v7 v8 v9
du_ana'7496''45''8764'_152 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666) ->
  AgdaAny -> AgdaAny -> AgdaAny -> T__'8764''7496'__12
du_ana'7496''45''8764'_152 v0 v1 v2 v3 v4 v5 v6
  = coe
      C_constructor_24
      (coe
         du_anaTree'45''8764'_170 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v1 v4) (coe v2 v5) (coe v3 v4 v5 v6))
-- Once.Denotation.ValueDomainLaws.anaTree-∼
d_anaTree'45''8764'_170 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
d_anaTree'45''8764'_170 v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_anaTree'45''8764'_170 v0 v4 v5 v6 v7 v8 v9
du_anaTree'45''8764'_170 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666) ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666
du_anaTree'45''8764'_170 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Once.Denotation.TraceMonad.C_rel'45'ret_678 v9
        -> case coe v4 of
             MAlonzo.Code.Once.Denotation.TraceMonad.C_ret_182 v10
               -> case coe v5 of
                    MAlonzo.Code.Once.Denotation.TraceMonad.C_ret_182 v11
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonad.C_rel'45'ret_678
                           (coe
                              du_mapAna'7496''45''8764'_190 (coe v0) (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v10) (coe v11) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonad.C_rel'45'call_690 v11
        -> case coe v4 of
             MAlonzo.Code.Once.Denotation.TraceMonad.C_call_186 v12 v13 v14
               -> case coe v5 of
                    MAlonzo.Code.Once.Denotation.TraceMonad.C_call_186 v15 v16 v17
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonad.C_rel'45'call_690
                           (\ v18 ->
                              coe
                                du_anaTree'45''8764'_170 (coe v0) (coe v1) (coe v2) (coe v3)
                                (coe v14 v18) (coe v17 v18) (coe v11 v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonad.C_rel'45'halt_696
        -> coe MAlonzo.Code.Once.Denotation.TraceMonad.C_rel'45'halt_696
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueDomainLaws.mapAnaᵈ-∼
d_mapAna'7496''45''8764'_190 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_mapAna'7496''45''8764'_190 v0 v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10
  = du_mapAna'7496''45''8764'_190 v0 v1 v5 v6 v7 v8 v9 v10
du_mapAna'7496''45''8764'_190 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_666) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_mapAna'7496''45''8764'_190 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v1 of
      MAlonzo.Code.Once.Semantics.Functor.C_SK_8 -> coe v7
      MAlonzo.Code.Once.Semantics.Functor.C_SId_10
        -> coe
             du_ana'7496''45''8764'_152 (coe v0) (coe v2) (coe v3) (coe v4)
             (coe v5) (coe v6) (coe v7)
      MAlonzo.Code.Once.Semantics.Functor.C__S'8853'__12 v8 v9
        -> case coe v5 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
               -> case coe v6 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> coe
                           du_mapAna'7496''45''8764'_190 (coe v0) (coe v8) (coe v2) (coe v3)
                           (coe v4) (coe v10) (coe v11) (coe v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
               -> case coe v6 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> coe
                           du_mapAna'7496''45''8764'_190 (coe v0) (coe v9) (coe v2) (coe v3)
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
                                     du_mapAna'7496''45''8764'_190 (coe v0) (coe v8) (coe v2)
                                     (coe v3) (coe v4) (coe v10) (coe v12) (coe v14))
                                  (coe
                                     du_mapAna'7496''45''8764'_190 (coe v0) (coe v9) (coe v2)
                                     (coe v3) (coe v4) (coe v11) (coe v13) (coe v15))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
