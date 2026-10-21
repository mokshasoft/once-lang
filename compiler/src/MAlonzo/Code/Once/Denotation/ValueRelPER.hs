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

module MAlonzo.Code.Once.Denotation.ValueRelPER where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Denotation.TraceMonadInfLaws
import qualified MAlonzo.Code.Once.Denotation.ValueRel
import qualified MAlonzo.Code.Once.Internal.FunctorMeaning
import qualified MAlonzo.Code.Once.Internal.Iterative
import qualified MAlonzo.Code.Once.Internal.Polynomial
import qualified MAlonzo.Code.Once.Internal.StreamInf
import qualified MAlonzo.Code.Once.Internal.Trace
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Spec.Grade

-- Once.Denotation.ValueRelPER.RelS-sym
d_RelS'45'sym_22 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_RelS'45'sym_22 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_RelS'45'sym_22 v4 v5 v6 v7
du_RelS'45'sym_22 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_RelS'45'sym_22 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_constructor_398
      (coe
         du_RelSB'45'sym_40 (coe v0)
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v1))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v2))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
            (coe v3)))
-- Once.Denotation.ValueRelPER.RelSB-sym
d_RelSB'45'sym_40 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
d_RelSB'45'sym_40 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_RelSB'45'sym_40 v4 v5 v6 v7
du_RelSB'45'sym_40 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
du_RelSB'45'sym_40 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v7
               -> case coe v7 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
                      -> case coe v2 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v9
                             -> case coe v9 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406
                                         (coe v0 v8 v10 v6)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v7
               -> case coe v7 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                      -> case coe v2 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v9
                             -> case coe v9 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412
                                         (coe
                                            du_RelS'45'sym_22 (coe v0) (coe v8) (coe v10) (coe v6))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Trace.C_call_118 v9 v10 v11
               -> case coe v2 of
                    MAlonzo.Code.Once.Internal.Trace.C_call_118 v12 v13 v14
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424
                           (\ v15 ->
                              coe
                                du_RelSB'45'sym_40 (coe v0) (coe v11 v15) (coe v14 v15)
                                (coe v8 v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueRelPER.RelS-trans
d_RelS'45'trans_86 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_RelS'45'trans_86 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11
  = du_RelS'45'trans_86 v6 v7 v8 v9 v10 v11
du_RelS'45'trans_86 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_RelS'45'trans_86 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_constructor_398
      (coe
         du_RelSB'45'trans_112 (coe v0)
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v1))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v2))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v3))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
            (coe v4))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
            (coe v5)))
-- Once.Denotation.ValueRelPER.RelSB-trans
d_RelSB'45'trans_112 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
d_RelSB'45'trans_112 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11
  = du_RelSB'45'trans_112 v6 v7 v8 v9 v10 v11
du_RelSB'45'trans_112 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
du_RelSB'45'trans_112 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v9
               -> case coe v9 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
                      -> case coe v2 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v11
                             -> case coe v11 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                                    -> case coe v5 of
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v15
                                           -> case coe v3 of
                                                MAlonzo.Code.Once.Internal.Trace.C_ret_114 v16
                                                  -> case coe v16 of
                                                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v17
                                                         -> coe
                                                              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406
                                                              (coe v0 v10 v12 v17 v8 v15)
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v9
               -> case coe v9 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                      -> case coe v2 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v11
                             -> case coe v11 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                                    -> case coe v5 of
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412 v15
                                           -> case coe v3 of
                                                MAlonzo.Code.Once.Internal.Trace.C_ret_114 v16
                                                  -> case coe v16 of
                                                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v17
                                                         -> coe
                                                              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412
                                                              (coe
                                                                 du_RelS'45'trans_86 (coe v0)
                                                                 (coe v10) (coe v12) (coe v17)
                                                                 (coe v8) (coe v15))
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Trace.C_call_118 v11 v12 v13
               -> case coe v2 of
                    MAlonzo.Code.Once.Internal.Trace.C_call_118 v14 v15 v16
                      -> case coe v5 of
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424 v21
                             -> case coe v3 of
                                  MAlonzo.Code.Once.Internal.Trace.C_call_118 v22 v23 v24
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424
                                         (\ v25 ->
                                            coe
                                              du_RelSB'45'trans_112 (coe v0) (coe v13 v25)
                                              (coe v16 v25) (coe v24 v25) (coe v10 v25)
                                              (coe v21 v25))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
        -> coe
             seq (coe v5)
             (coe
                MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueRelPER.RelS-meet
d_RelS'45'meet_164 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_RelS'45'meet_164 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9
  = du_RelS'45'meet_164 v5 v6 v7 v8 v9
du_RelS'45'meet_164 ::
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_RelS'45'meet_164 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_constructor_398
      (coe
         du_RelSB'45'meet_188
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v0))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v1))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v2))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
            (coe v3))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
            (coe v4)))
-- Once.Denotation.ValueRelPER.RelSB-meet
d_RelSB'45'meet_188 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
d_RelSB'45'meet_188 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9
  = du_RelSB'45'meet_188 v5 v6 v7 v8 v9
du_RelSB'45'meet_188 ::
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
du_RelSB'45'meet_188 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v7
        -> case coe v2 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v8
               -> case coe v8 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> case coe v4 of
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v12
                             -> coe
                                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                                        (coe v12)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v8
               -> case coe v8 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> case coe v2 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v10
                             -> case coe v10 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                                    -> case coe v4 of
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412 v14
                                           -> case coe v1 of
                                                MAlonzo.Code.Once.Internal.Trace.C_ret_114 v15
                                                  -> case coe v15 of
                                                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v16
                                                         -> coe
                                                              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412
                                                              (coe
                                                                 du_RelS'45'meet_164 (coe v9)
                                                                 (coe v16) (coe v11) (coe v7)
                                                                 (coe v14))
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Trace.C_call_118 v10 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Internal.Trace.C_call_118 v13 v14 v15
                      -> case coe v4 of
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424 v20
                             -> case coe v1 of
                                  MAlonzo.Code.Once.Internal.Trace.C_call_118 v21 v22 v23
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424
                                         (\ v24 ->
                                            coe
                                              du_RelSB'45'meet_188 (coe v12 v24) (coe v23 v24)
                                              (coe v15 v24) (coe v9 v24) (coe v20 v24))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
        -> coe
             seq (coe v4)
             (coe
                MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueRelPER.RelS-rightself
d_RelS'45'rightself_224 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_RelS'45'rightself_224 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_RelS'45'rightself_224 v4 v5 v6 v7
du_RelS'45'rightself_224 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_RelS'45'rightself_224 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_constructor_398
      (coe
         du_RelSB'45'rightself_242 (coe v0)
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v1))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v2))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
            (coe v3)))
-- Once.Denotation.ValueRelPER.RelSB-rightself
d_RelSB'45'rightself_242 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
d_RelSB'45'rightself_242 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_RelSB'45'rightself_242 v4 v5 v6 v7
du_RelSB'45'rightself_242 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
du_RelSB'45'rightself_242 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v7
               -> case coe v7 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
                      -> case coe v2 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v9
                             -> case coe v9 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406
                                         (coe v0 v8 v10 v6)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v7
               -> case coe v7 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                      -> case coe v2 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v9
                             -> case coe v9 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412
                                         (coe
                                            du_RelS'45'rightself_224 (coe v0) (coe v8) (coe v10)
                                            (coe v6))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Trace.C_call_118 v9 v10 v11
               -> case coe v2 of
                    MAlonzo.Code.Once.Internal.Trace.C_call_118 v12 v13 v14
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424
                           (\ v15 ->
                              coe
                                du_RelSB'45'rightself_242 (coe v0) (coe v11 v15) (coe v14 v15)
                                (coe v8 v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueRelPER.RelS-pairʳ
d_RelS'45'pair'691'_280 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_RelS'45'pair'691'_280 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_RelS'45'pair'691'_280 v4 v5 v6 v7
du_RelS'45'pair'691'_280 ::
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
du_RelS'45'pair'691'_280 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_constructor_398
      (coe
         du_RelSB'45'pair'691'_298
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v0))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v1))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
            (coe v2))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
            (coe v3)))
-- Once.Denotation.ValueRelPER.RelSB-pairʳ
d_RelSB'45'pair'691'_298 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
d_RelSB'45'pair'691'_298 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_RelSB'45'pair'691'_298 v4 v5 v6 v7
du_RelSB'45'pair'691'_298 ::
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
du_RelSB'45'pair'691'_298 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v6
        -> case coe v3 of
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v9
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v7
               -> case coe v7 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                      -> case coe v1 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v9
                             -> case coe v9 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                                    -> case coe v3 of
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412 v13
                                           -> coe
                                                MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412
                                                (coe
                                                   du_RelS'45'pair'691'_280 (coe v8) (coe v10)
                                                   (coe v6) (coe v13))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Trace.C_call_118 v9 v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Trace.C_call_118 v12 v13 v14
                      -> case coe v3 of
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424 v19
                             -> coe
                                  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424
                                  (\ v20 ->
                                     coe
                                       du_RelSB'45'pair'691'_298 (coe v11 v20) (coe v14 v20)
                                       (coe v8 v20) (coe v19 v20))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
        -> coe
             seq (coe v3)
             (coe
                MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueRelPER._.stream-sym
d_stream'45'sym_328 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  MAlonzo.Code.Once.Denotation.ValueRel.T_StreamRel_16 ->
  MAlonzo.Code.Once.Denotation.ValueRel.T_StreamRel_16
d_stream'45'sym_328 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.C_constructor_34
      (coe
         d_run'45'sym_334 (coe v0)
         (coe
            MAlonzo.Code.Once.Internal.StreamInf.d_force'7477'_20 (coe v1))
         (coe
            MAlonzo.Code.Once.Internal.StreamInf.d_force'7477'_20 (coe v2))
         (coe MAlonzo.Code.Once.Denotation.ValueRel.d_forceR_32 (coe v3)))
-- Once.Denotation.ValueRelPER._.run-sym
d_run'45'sym_334 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_run'45'sym_334 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_constructor_398
      (coe
         d_block'45'sym_340 (coe v0)
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v1))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v2))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
            (coe v3)))
-- Once.Denotation.ValueRelPER._.block-sym
d_block'45'sym_340 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
d_block'45'sym_340 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v7
               -> case coe v7 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
                      -> case coe v2 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v9
                             -> case coe v9 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406
                                         (d_layer'45'sym_348
                                            (coe v0) (coe v0) (coe v8) (coe v10) (coe v6))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v7
               -> case coe v7 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                      -> case coe v2 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v9
                             -> case coe v9 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412
                                         (d_run'45'sym_334 (coe v0) (coe v8) (coe v10) (coe v6))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Trace.C_call_118 v9 v10 v11
               -> case coe v2 of
                    MAlonzo.Code.Once.Internal.Trace.C_call_118 v12 v13 v14
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424
                           (\ v15 ->
                              d_block'45'sym_340
                                (coe v0) (coe v11 v15) (coe v14 v15) (coe v8 v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueRelPER._.layer-sym
d_layer'45'sym_348 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_layer'45'sym_348 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Internal.Polynomial.C_SK_8 -> erased
      MAlonzo.Code.Once.Internal.Polynomial.C_SId_10
        -> coe d_stream'45'sym_328 (coe v0) (coe v2) (coe v3) (coe v4)
      MAlonzo.Code.Once.Internal.Polynomial.C__S'8853'__12 v5 v6
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
                      -> coe
                           d_layer'45'sym_348 (coe v0) (coe v5) (coe v7) (coe v8) (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                      -> coe
                           d_layer'45'sym_348 (coe v0) (coe v6) (coe v7) (coe v8) (coe v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Polynomial.C__S'8855'__14 v5 v6
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> case coe v4 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe
                                     d_layer'45'sym_348 (coe v0) (coe v5) (coe v7) (coe v9)
                                     (coe v11))
                                  (coe
                                     d_layer'45'sym_348 (coe v0) (coe v6) (coe v8) (coe v10)
                                     (coe v12))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueRelPER._.stream-trans
d_stream'45'trans_402 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  MAlonzo.Code.Once.Internal.StreamInf.T_ν'7477'_14 ->
  MAlonzo.Code.Once.Denotation.ValueRel.T_StreamRel_16 ->
  MAlonzo.Code.Once.Denotation.ValueRel.T_StreamRel_16 ->
  MAlonzo.Code.Once.Denotation.ValueRel.T_StreamRel_16
d_stream'45'trans_402 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Denotation.ValueRel.C_constructor_34
      (coe
         d_run'45'trans_410 (coe v0)
         (coe
            MAlonzo.Code.Once.Internal.StreamInf.d_force'7477'_20 (coe v1))
         (coe
            MAlonzo.Code.Once.Internal.StreamInf.d_force'7477'_20 (coe v2))
         (coe
            MAlonzo.Code.Once.Internal.StreamInf.d_force'7477'_20 (coe v3))
         (coe MAlonzo.Code.Once.Denotation.ValueRel.d_forceR_32 (coe v4))
         (coe MAlonzo.Code.Once.Denotation.ValueRel.d_forceR_32 (coe v5)))
-- Once.Denotation.ValueRelPER._.run-trans
d_run'45'trans_410 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelS_378
d_run'45'trans_410 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_constructor_398
      (coe
         d_block'45'trans_418 (coe v0)
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v1))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v2))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v3))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
            (coe v4))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.d_forceS_396
            (coe v5)))
-- Once.Denotation.ValueRelPER._.block-trans
d_block'45'trans_418 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386 ->
  MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.T_RelSB_386
d_block'45'trans_418 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v9
               -> case coe v9 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
                      -> case coe v2 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v11
                             -> case coe v11 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                                    -> case coe v5 of
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406 v15
                                           -> case coe v3 of
                                                MAlonzo.Code.Once.Internal.Trace.C_ret_114 v16
                                                  -> case coe v16 of
                                                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v17
                                                         -> coe
                                                              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'ret_406
                                                              (d_layer'45'trans_428
                                                                 (coe v0) (coe v0) (coe v10)
                                                                 (coe v12) (coe v17) (coe v8)
                                                                 (coe v15))
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v9
               -> case coe v9 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                      -> case coe v2 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v11
                             -> case coe v11 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                                    -> case coe v5 of
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412 v15
                                           -> case coe v3 of
                                                MAlonzo.Code.Once.Internal.Trace.C_ret_114 v16
                                                  -> case coe v16 of
                                                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v17
                                                         -> coe
                                                              MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'next_412
                                                              (d_run'45'trans_410
                                                                 (coe v0) (coe v10) (coe v12)
                                                                 (coe v17) (coe v8) (coe v15))
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Trace.C_call_118 v11 v12 v13
               -> case coe v2 of
                    MAlonzo.Code.Once.Internal.Trace.C_call_118 v14 v15 v16
                      -> case coe v5 of
                           MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424 v21
                             -> case coe v3 of
                                  MAlonzo.Code.Once.Internal.Trace.C_call_118 v22 v23 v24
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'call_424
                                         (\ v25 ->
                                            d_block'45'trans_418
                                              (coe v0) (coe v13 v25) (coe v16 v25) (coe v24 v25)
                                              (coe v10 v25) (coe v21 v25))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430
        -> coe
             seq (coe v5)
             (coe
                MAlonzo.Code.Once.Denotation.TraceMonadInfLaws.C_s'45'halt_430)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueRelPER._.layer-trans
d_layer'45'trans_428 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_layer'45'trans_428 v0 v1 v2 v3 v4 v5 v6
  = case coe v1 of
      MAlonzo.Code.Once.Internal.Polynomial.C_SK_8 -> erased
      MAlonzo.Code.Once.Internal.Polynomial.C_SId_10
        -> coe
             d_stream'45'trans_402 (coe v0) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe v6)
      MAlonzo.Code.Once.Internal.Polynomial.C__S'8853'__12 v7 v8
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
                      -> case coe v4 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                             -> coe
                                  d_layer'45'trans_428 (coe v0) (coe v7) (coe v9) (coe v10)
                                  (coe v11) (coe v5) (coe v6)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                      -> case coe v4 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                             -> coe
                                  d_layer'45'trans_428 (coe v0) (coe v8) (coe v9) (coe v10)
                                  (coe v11) (coe v5) (coe v6)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Polynomial.C__S'8855'__14 v7 v8
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                      -> case coe v4 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                             -> case coe v5 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                    -> case coe v6 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe
                                                   d_layer'45'trans_428 (coe v0) (coe v7) (coe v9)
                                                   (coe v11) (coe v13) (coe v15) (coe v17))
                                                (coe
                                                   d_layer'45'trans_428 (coe v0) (coe v8) (coe v10)
                                                   (coe v12) (coe v14) (coe v16) (coe v18))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueRelPER.RelD-sym
d_RelD'45'sym_512 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_RelD'45'sym_512 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Type.C_Unit_20
        -> coe (\ v3 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C__'42'__24 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                      -> coe
                           (\ v9 ->
                              case coe v9 of
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                  -> coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                       (coe d_RelD'45'sym_512 v3 v5 v7 v10)
                                       (coe d_RelD'45'sym_512 v4 v6 v8 v11)
                                _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C__'43'__26 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
                      -> coe (\ v7 -> coe d_RelD'45'sym_512 v3 v5 v6 v7)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
                      -> coe (\ v7 -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
                      -> coe (\ v7 -> MAlonzo.RTE.mazUnreachableError)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
                      -> coe (\ v7 -> coe d_RelD'45'sym_512 v4 v5 v6 v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                      -> coe
                           (\ v8 ->
                              coe
                                du_RelS'45'sym_22 (coe d_RelD'45'sym_512 (coe v5))
                                (coe v1 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                (coe v2 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)) (coe v8))
                    MAlonzo.Code.Once.Spec.Grade.C_One_10
                      -> coe
                           (\ v8 v9 v10 v11 ->
                              coe
                                du_RelS'45'sym_22 (coe d_RelD'45'sym_512 (coe v5)) (coe v1 v10)
                                (coe v2 v9) (coe v8 v10 v9 (coe d_RelD'45'sym_512 v3 v9 v10 v11)))
                    MAlonzo.Code.Once.Spec.Grade.C_Many_12
                      -> coe
                           (\ v8 v9 v10 v11 ->
                              coe
                                du_RelS'45'sym_22 (coe d_RelD'45'sym_512 (coe v5)) (coe v1 v10)
                                (coe v2 v9) (coe v8 v10 v9 (coe d_RelD'45'sym_512 v3 v9 v10 v11)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v3 -> erased
      MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v3 v4
        -> coe
             (\ v5 ->
                d_stream'45'sym_328
                  (coe
                     MAlonzo.Code.Once.Internal.FunctorMeaning.du_translateF_56
                     (coe v3))
                  (coe v1) (coe v2) (coe v5))
      MAlonzo.Code.Once.Internal.Type.C_Int_34 -> erased
      MAlonzo.Code.Once.Internal.Type.C_Float_36 -> erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueRelPER.RelD-trans
d_RelD'45'trans_522 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_RelD'45'trans_522 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Type.C_Unit_20
        -> coe (\ v4 v5 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Internal.Type.C__'42'__24 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                             -> coe
                                  (\ v12 ->
                                     case coe v12 of
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                         -> coe
                                              (\ v15 ->
                                                 case coe v15 of
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                     -> coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             d_RelD'45'trans_522 v4 v6 v8 v10 v13
                                                             v16)
                                                          (coe
                                                             d_RelD'45'trans_522 v5 v7 v9 v11 v14
                                                             v17)
                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C__'43'__26 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
                             -> coe (\ v9 v10 -> coe d_RelD'45'trans_522 v4 v6 v7 v8 v9 v10)
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                             -> coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
                      -> coe (\ v8 v9 -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
                      -> coe (\ v8 v9 -> MAlonzo.RTE.mazUnreachableError)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
                             -> coe (\ v9 v10 -> MAlonzo.RTE.mazUnreachableError)
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                             -> coe (\ v9 v10 -> coe d_RelD'45'trans_522 v5 v6 v7 v8 v9 v10)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v4 v5 v6
        -> case coe v5 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v7 v8
               -> case coe v7 of
                    MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                      -> coe
                           (\ v9 v10 ->
                              coe
                                du_RelS'45'trans_86 (coe d_RelD'45'trans_522 (coe v6))
                                (coe v1 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                (coe v2 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                (coe v3 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)) (coe v9)
                                (coe v10))
                    MAlonzo.Code.Once.Spec.Grade.C_One_10
                      -> coe
                           (\ v9 v10 v11 v12 v13 ->
                              coe
                                du_RelS'45'trans_86 (coe d_RelD'45'trans_522 (coe v6)) (coe v1 v11)
                                (coe v2 v12) (coe v3 v12) (coe v9 v11 v12 v13)
                                (coe
                                   v10 v12 v12
                                   (d_RelD'45'rightself_530
                                      (coe v4) (coe v11) (coe v12) (coe v13))))
                    MAlonzo.Code.Once.Spec.Grade.C_Many_12
                      -> coe
                           (\ v9 v10 v11 v12 v13 ->
                              coe
                                du_RelS'45'trans_86 (coe d_RelD'45'trans_522 (coe v6)) (coe v1 v11)
                                (coe v2 v12) (coe v3 v12) (coe v9 v11 v12 v13)
                                (coe
                                   v10 v12 v12
                                   (d_RelD'45'rightself_530
                                      (coe v4) (coe v11) (coe v12) (coe v13))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Type.C_μ'45'type_30 v4 -> erased
      MAlonzo.Code.Once.Internal.Type.C_ν'45'type_32 v4 v5
        -> coe
             (\ v6 v7 ->
                d_stream'45'trans_402
                  (coe
                     MAlonzo.Code.Once.Internal.FunctorMeaning.du_translateF_56
                     (coe v4))
                  (coe v1) (coe v2) (coe v3) (coe v6) (coe v7))
      MAlonzo.Code.Once.Internal.Type.C_Int_34 -> erased
      MAlonzo.Code.Once.Internal.Type.C_Float_36 -> erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.ValueRelPER.RelD-rightself
d_RelD'45'rightself_530 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_RelD'45'rightself_530 v0 v1 v2 v3
  = coe
      d_RelD'45'trans_522 v0 v2 v1 v2 (coe d_RelD'45'sym_512 v0 v1 v2 v3)
      v3
-- Once.Denotation.ValueRelPER.RelD-leftself
d_RelD'45'leftself_718 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_RelD'45'leftself_718 v0 v1 v2 v3
  = coe
      d_RelD'45'trans_522 v0 v1 v2 v1 v3
      (coe d_RelD'45'sym_512 v0 v1 v2 v3)
