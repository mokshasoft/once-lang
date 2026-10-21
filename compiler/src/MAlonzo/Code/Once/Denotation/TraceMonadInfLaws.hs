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

module MAlonzo.Code.Once.Denotation.TraceMonadInfLaws where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Internal.Iterative
import qualified MAlonzo.Code.Once.Internal.Trace

-- Once.Denotation.TraceMonadInfLaws.≈∞-refl
d_'8776''8734''45'refl_14 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_TreeEq'8734'_334
d_'8776''8734''45'refl_14 ~v0 ~v1 v2 v3
  = du_'8776''8734''45'refl_14 v2 v3
du_'8776''8734''45'refl_14 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_TreeEq'8734'_334
du_'8776''8734''45'refl_14 v0 v1
  = coe
      MAlonzo.Code.Once.Internal.Iterative.C_constructor_348
      (coe
         du_'8776''8734''45'reflB_24 (coe v0)
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v1)))
-- Once.Denotation.TraceMonadInfLaws.≈∞-reflB
d_'8776''8734''45'reflB_24 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Iterative.T_BlockEq_266
d_'8776''8734''45'reflB_24 ~v0 ~v1 v2 v3
  = du_'8776''8734''45'reflB_24 v2 v3
du_'8776''8734''45'reflB_24 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Iterative.T_BlockEq_266
du_'8776''8734''45'reflB_24 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Internal.Trace.C_ret_114 v2
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
               -> coe
                    MAlonzo.Code.Once.Internal.Iterative.C_ret'8776'_276
                    (coe
                       MAlonzo.Code.Once.Internal.Iterative.C_done'8776'_318 (coe v0 v3))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
               -> coe
                    MAlonzo.Code.Once.Internal.Iterative.C_ret'8776'_276
                    (coe
                       MAlonzo.Code.Once.Internal.Iterative.C_next'8776'_324
                       (coe du_'8776''8734''45'refl_14 (coe v0) (coe v3)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Trace.C_call_118 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Internal.Iterative.C_call'8776'_288
             (\ v5 -> coe du_'8776''8734''45'reflB_24 (coe v0) (coe v4 v5))
      MAlonzo.Code.Once.Internal.Trace.C_halt_122 v2 v3
        -> coe MAlonzo.Code.Once.Internal.Iterative.C_halt'8776'_294
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws.≈∞-bind
d_'8776''8734''45'bind_74 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Internal.Iterative.T_TreeEq'8734'_334 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Internal.Iterative.T_TreeEq'8734'_334) ->
  MAlonzo.Code.Once.Internal.Iterative.T_TreeEq'8734'_334
d_'8776''8734''45'bind_74 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_'8776''8734''45'bind_74 v4 v5 v6 v7 v8 v9
du_'8776''8734''45'bind_74 ::
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Internal.Iterative.T_TreeEq'8734'_334 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Internal.Iterative.T_TreeEq'8734'_334) ->
  MAlonzo.Code.Once.Internal.Iterative.T_TreeEq'8734'_334
du_'8776''8734''45'bind_74 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Internal.Iterative.C_constructor_348
      (coe
         du_'8776''8734''45'bindB_96
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v0))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v1))
         (coe v2) (coe v3)
         (coe
            MAlonzo.Code.Once.Internal.Iterative.d_force'8776'_346 (coe v4))
         (coe v5))
-- Once.Denotation.TraceMonadInfLaws.≈∞-bindB
d_'8776''8734''45'bindB_96 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Internal.Iterative.T_BlockEq_266 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Internal.Iterative.T_TreeEq'8734'_334) ->
  MAlonzo.Code.Once.Internal.Iterative.T_BlockEq_266
d_'8776''8734''45'bindB_96 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_'8776''8734''45'bindB_96 v4 v5 v6 v7 v8 v9
du_'8776''8734''45'bindB_96 ::
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Internal.Iterative.T_BlockEq_266 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Once.Internal.Iterative.T_TreeEq'8734'_334) ->
  MAlonzo.Code.Once.Internal.Iterative.T_BlockEq_266
du_'8776''8734''45'bindB_96 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Once.Internal.Iterative.C_ret'8776'_276 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Trace.C_ret_114 v10
                      -> case coe v8 of
                           MAlonzo.Code.Once.Internal.Iterative.C_done'8776'_318 v13
                             -> case coe v9 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v14
                                    -> case coe v10 of
                                         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v15
                                           -> coe
                                                MAlonzo.Code.Once.Internal.Iterative.d_force'8776'_346
                                                (coe v5 v14 v15 v13)
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Internal.Iterative.C_next'8776'_324 v13
                             -> case coe v9 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v14
                                    -> case coe v10 of
                                         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v15
                                           -> coe
                                                MAlonzo.Code.Once.Internal.Iterative.C_ret'8776'_276
                                                (coe
                                                   MAlonzo.Code.Once.Internal.Iterative.C_next'8776'_324
                                                   (coe
                                                      du_'8776''8734''45'bind_74 (coe v14) (coe v15)
                                                      (coe v2) (coe v3) (coe v13) (coe v5)))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Iterative.C_call'8776'_288 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Trace.C_call_118 v11 v12 v13
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Trace.C_call_118 v14 v15 v16
                      -> coe
                           MAlonzo.Code.Once.Internal.Iterative.C_call'8776'_288
                           (\ v17 ->
                              coe
                                du_'8776''8734''45'bindB_96 (coe v13 v17) (coe v16 v17) (coe v2)
                                (coe v3) (coe v10 v17) (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Iterative.C_halt'8776'_294
        -> coe MAlonzo.Code.Once.Internal.Iterative.C_halt'8776'_294
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws.≈∞-idˡ
d_'8776''8734''45'id'737'_126 ::
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Internal.Iterative.T_TreeEq'8734'_334
d_'8776''8734''45'id'737'_126 ~v0 ~v1 v2 v3
  = du_'8776''8734''45'id'737'_126 v2 v3
du_'8776''8734''45'id'737'_126 ::
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Internal.Iterative.T_TreeEq'8734'_334
du_'8776''8734''45'id'737'_126 v0 v1
  = coe
      MAlonzo.Code.Once.Internal.Iterative.C_constructor_348
      (coe
         du_'8776''8734''45'reflB_24 erased
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v1 v0)))
-- Once.Denotation.TraceMonadInfLaws.RelB
d_RelB_140 a0 a1 a2 a3 a4 = ()
data T_RelB_140
  = C_b'45'ret_152 AgdaAny | C_b'45'tau_158 T_RelB_140 |
    C_b'45'call_170 (AgdaAny -> T_RelB_140) | C_b'45'halt_176
-- Once.Denotation.TraceMonadInfLaws.RelT∞′
d_RelT'8734''8242'_188 a0 a1 a2 a3 a4 = ()
newtype T_RelT'8734''8242'_188 = C_rel'8734'_204 T_RelB_140
-- Once.Denotation.TraceMonadInfLaws.RelT∞′.block
d_block_202 :: T_RelT'8734''8242'_188 -> T_RelB_140
d_block_202 v0
  = case coe v0 of
      C_rel'8734'_204 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws.rel∞-ret
d_rel'8734''45'ret_216 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> AgdaAny -> T_RelT'8734''8242'_188
d_rel'8734''45'ret_216 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_rel'8734''45'ret_216 v5
du_rel'8734''45'ret_216 :: AgdaAny -> T_RelT'8734''8242'_188
du_rel'8734''45'ret_216 v0
  = coe C_rel'8734'_204 (coe C_b'45'ret_152 v0)
-- Once.Denotation.TraceMonadInfLaws.RelB-bind
d_RelB'45'bind_244 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Trace.T_T_110) ->
  T_RelB_140 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> T_RelT'8734''8242'_188) ->
  T_RelB_140
d_RelB'45'bind_244 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9 v10 v11
  = du_RelB'45'bind_244 v6 v7 v10 v11
du_RelB'45'bind_244 ::
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  T_RelB_140 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> T_RelT'8734''8242'_188) ->
  T_RelB_140
du_RelB'45'bind_244 v0 v1 v2 v3
  = case coe v2 of
      C_b'45'ret_152 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v7
               -> case coe v7 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
                      -> case coe v1 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v9
                             -> coe d_block_202 (coe v3 v8 v9 v6)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_b'45'tau_158 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v7
               -> case coe v7 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                      -> coe
                           C_b'45'tau_158
                           (coe
                              du_RelB'45'bind_244
                              (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v8))
                              (coe v1) (coe v6) (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_b'45'call_170 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Trace.C_call_118 v9 v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Trace.C_call_118 v12 v13 v14
                      -> coe
                           C_b'45'call_170
                           (\ v15 ->
                              coe
                                du_RelB'45'bind_244 (coe v11 v15) (coe v14 v15) (coe v8 v15)
                                (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_b'45'halt_176 -> coe C_b'45'halt_176
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws.RelT∞′-bind
d_RelT'8734''8242''45'bind_286 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Trace.T_T_110) ->
  T_RelT'8734''8242'_188 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> T_RelT'8734''8242'_188) ->
  T_RelT'8734''8242'_188
d_RelT'8734''8242''45'bind_286 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8
                               ~v9 v10 v11
  = du_RelT'8734''8242''45'bind_286 v6 v7 v10 v11
du_RelT'8734''8242''45'bind_286 ::
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  T_RelT'8734''8242'_188 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> T_RelT'8734''8242'_188) ->
  T_RelT'8734''8242'_188
du_RelT'8734''8242''45'bind_286 v0 v1 v2 v3
  = case coe v2 of
      C_rel'8734'_204 v4
        -> coe
             C_rel'8734'_204
             (coe
                du_RelB'45'bind_244
                (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v0))
                (coe v1) (coe v4) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws.RelB-≈
d_RelB'45''8776'_304 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Iterative.T_BlockEq_266 ->
  T_RelB_140 -> T_RelB_140
d_RelB'45''8776'_304 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_RelB'45''8776'_304 v3 v4 v5 v6 v7
du_RelB'45''8776'_304 ::
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Iterative.T_BlockEq_266 ->
  T_RelB_140 -> T_RelB_140
du_RelB'45''8776'_304 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Internal.Iterative.C_ret'8776'_276 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v8
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Trace.C_ret_114 v9
                      -> case coe v7 of
                           MAlonzo.Code.Once.Internal.Iterative.C_done'8776'_318 v12
                             -> case coe v4 of
                                  C_b'45'ret_152 v15 -> coe C_b'45'ret_152 v15
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Internal.Iterative.C_next'8776'_324 v12
                             -> case coe v8 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
                                    -> case coe v9 of
                                         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v14
                                           -> case coe v4 of
                                                C_b'45'tau_158 v17
                                                  -> coe
                                                       C_b'45'tau_158
                                                       (coe
                                                          du_RelB'45''8776'_304
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Iterative.d_force_64
                                                             (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Iterative.d_force_64
                                                             (coe v14))
                                                          (coe v2)
                                                          (coe
                                                             MAlonzo.Code.Once.Internal.Iterative.d_force'8776'_346
                                                             (coe v12))
                                                          (coe v17))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Iterative.C_call'8776'_288 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Trace.C_call_118 v10 v11 v12
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Trace.C_call_118 v13 v14 v15
                      -> case coe v4 of
                           C_b'45'call_170 v20
                             -> case coe v2 of
                                  MAlonzo.Code.Once.Internal.Trace.C_call_118 v21 v22 v23
                                    -> coe
                                         C_b'45'call_170
                                         (\ v24 ->
                                            coe
                                              du_RelB'45''8776'_304 (coe v12 v24) (coe v15 v24)
                                              (coe v23 v24) (coe v9 v24) (coe v20 v24))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Iterative.C_halt'8776'_294
        -> coe seq (coe v4) (coe C_b'45'halt_176)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws.RelT∞′-≈
d_RelT'8734''8242''45''8776'_330 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Iterative.T_TreeEq'8734'_334 ->
  T_RelT'8734''8242'_188 -> T_RelT'8734''8242'_188
d_RelT'8734''8242''45''8776'_330 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_RelT'8734''8242''45''8776'_330 v3 v4 v5 v6 v7
du_RelT'8734''8242''45''8776'_330 ::
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Iterative.T_TreeEq'8734'_334 ->
  T_RelT'8734''8242'_188 -> T_RelT'8734''8242'_188
du_RelT'8734''8242''45''8776'_330 v0 v1 v2 v3 v4
  = case coe v4 of
      C_rel'8734'_204 v5
        -> coe
             C_rel'8734'_204
             (coe
                du_RelB'45''8776'_304
                (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v0))
                (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v1))
                (coe v2)
                (coe
                   MAlonzo.Code.Once.Internal.Iterative.d_force'8776'_346 (coe v3))
                (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws.RelB-embed
d_RelB'45'embed_346 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_RelT'8242'_542 -> T_RelB_140
d_RelB'45'embed_346 ~v0 ~v1 ~v2 v3 v4 v5
  = du_RelB'45'embed_346 v3 v4 v5
du_RelB'45'embed_346 ::
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_RelT'8242'_542 -> T_RelB_140
du_RelB'45'embed_346 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Internal.Trace.C_rel'45'ret_554 v5
        -> coe C_b'45'ret_152 v5
      MAlonzo.Code.Once.Internal.Trace.C_rel'45'call_566 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Trace.C_call_118 v8 v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Trace.C_call_118 v11 v12 v13
                      -> coe
                           C_b'45'call_170
                           (\ v14 ->
                              coe du_RelB'45'embed_346 (coe v10 v14) (coe v13 v14) (coe v7 v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Trace.C_rel'45'halt_572
        -> coe C_b'45'halt_176
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws.RelT∞′-embed
d_RelT'8734''8242''45'embed_364 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_RelT'8242'_542 ->
  T_RelT'8734''8242'_188
d_RelT'8734''8242''45'embed_364 ~v0 ~v1 ~v2 v3 v4 v5
  = du_RelT'8734''8242''45'embed_364 v3 v4 v5
du_RelT'8734''8242''45'embed_364 ::
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_RelT'8242'_542 ->
  T_RelT'8734''8242'_188
du_RelT'8734''8242''45'embed_364 v0 v1 v2
  = coe
      C_rel'8734'_204
      (coe du_RelB'45'embed_346 (coe v0) (coe v1) (coe v2))
-- Once.Denotation.TraceMonadInfLaws.RelS
d_RelS_378 a0 a1 a2 a3 a4 = ()
data T_RelS_378 = C_constructor_398 T_RelSB_386
-- Once.Denotation.TraceMonadInfLaws.RelSB
d_RelSB_386 a0 a1 a2 a3 a4 = ()
data T_RelSB_386
  = C_s'45'ret_406 AgdaAny | C_s'45'next_412 T_RelS_378 |
    C_s'45'call_424 (AgdaAny -> T_RelSB_386) | C_s'45'halt_430
-- Once.Denotation.TraceMonadInfLaws.RelS.forceS
d_forceS_396 :: T_RelS_378 -> T_RelSB_386
d_forceS_396 v0
  = case coe v0 of
      C_constructor_398 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws.relS-ret
d_relS'45'ret_442 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> AgdaAny -> T_RelS_378
d_relS'45'ret_442 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_relS'45'ret_442 v5
du_relS'45'ret_442 :: AgdaAny -> T_RelS_378
du_relS'45'ret_442 v0
  = coe C_constructor_398 (coe C_s'45'ret_406 v0)
-- Once.Denotation.TraceMonadInfLaws.RelS-bind
d_RelS'45'bind_470 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  T_RelS_378 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> T_RelS_378) -> T_RelS_378
d_RelS'45'bind_470 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11
  = du_RelS'45'bind_470 v6 v7 v8 v9 v10 v11
du_RelS'45'bind_470 ::
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  T_RelS_378 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> T_RelS_378) -> T_RelS_378
du_RelS'45'bind_470 v0 v1 v2 v3 v4 v5
  = coe
      C_constructor_398
      (coe
         du_RelSB'45'bind_496
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v0))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v1))
         (coe v2) (coe v3) (coe d_forceS_396 (coe v4)) (coe v5))
-- Once.Denotation.TraceMonadInfLaws.RelSB-bind
d_RelSB'45'bind_496 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  T_RelSB_386 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> T_RelS_378) -> T_RelSB_386
d_RelSB'45'bind_496 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11
  = du_RelSB'45'bind_496 v6 v7 v8 v9 v10 v11
du_RelSB'45'bind_496 ::
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  T_RelSB_386 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> T_RelS_378) -> T_RelSB_386
du_RelSB'45'bind_496 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      C_s'45'ret_406 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v9
               -> case coe v9 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v10
                      -> case coe v1 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v11
                             -> case coe v11 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                                    -> coe d_forceS_396 (coe v5 v10 v12 v8)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_s'45'next_412 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v9
               -> case coe v9 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                      -> case coe v1 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v11
                             -> case coe v11 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                                    -> coe
                                         C_s'45'next_412
                                         (coe
                                            du_RelS'45'bind_470 (coe v10) (coe v12) (coe v2)
                                            (coe v3) (coe v8) (coe v5))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_s'45'call_424 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Trace.C_call_118 v11 v12 v13
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Trace.C_call_118 v14 v15 v16
                      -> coe
                           C_s'45'call_424
                           (\ v17 ->
                              coe
                                du_RelSB'45'bind_496 (coe v13 v17) (coe v16 v17) (coe v2) (coe v3)
                                (coe v10 v17) (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_s'45'halt_430 -> coe C_s'45'halt_430
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws._.RelS-iterRun
d_RelS'45'iterRun_566 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> T_RelS_378) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  T_RelS_378 -> T_RelS_378
d_RelS'45'iterRun_566 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 ~v11
                      v12 v13 v14
  = du_RelS'45'iterRun_566 v6 v7 v8 v9 v12 v13 v14
du_RelS'45'iterRun_566 ::
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> T_RelS_378) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  T_RelS_378 -> T_RelS_378
du_RelS'45'iterRun_566 v0 v1 v2 v3 v4 v5 v6
  = coe
      C_constructor_398
      (coe
         du_RelSB'45'iterBlock_572 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v4))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v5))
         (coe d_forceS_396 (coe v6)))
-- Once.Denotation.TraceMonadInfLaws._.RelSB-iterBlock
d_RelSB'45'iterBlock_572 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> T_RelS_378) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  T_RelSB_386 -> T_RelSB_386
d_RelSB'45'iterBlock_572 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10
                         ~v11 v12 v13 v14
  = du_RelSB'45'iterBlock_572 v6 v7 v8 v9 v12 v13 v14
du_RelSB'45'iterBlock_572 ::
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> T_RelS_378) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  T_RelSB_386 -> T_RelSB_386
du_RelSB'45'iterBlock_572 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      C_s'45'ret_406 v9
        -> case coe v4 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v10
               -> case coe v10 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> case coe v5 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v12
                             -> case coe v12 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13
                                    -> coe
                                         du_iter'45'ret_578 (coe v0) (coe v1) (coe v2) (coe v3)
                                         (coe v11) (coe v13) (coe v9)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_s'45'next_412 v9
        -> case coe v4 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v10
               -> case coe v10 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> case coe v5 of
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114 v12
                             -> case coe v12 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
                                    -> coe
                                         C_s'45'next_412
                                         (coe
                                            du_RelS'45'iterRun_566 (coe v0) (coe v1) (coe v2)
                                            (coe v3) (coe v11) (coe v13) (coe v9))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_s'45'call_424 v11
        -> case coe v4 of
             MAlonzo.Code.Once.Internal.Trace.C_call_118 v12 v13 v14
               -> case coe v5 of
                    MAlonzo.Code.Once.Internal.Trace.C_call_118 v15 v16 v17
                      -> coe
                           C_s'45'call_424
                           (\ v18 ->
                              coe
                                du_RelSB'45'iterBlock_572 (coe v0) (coe v1) (coe v2) (coe v3)
                                (coe v14 v18) (coe v17 v18) (coe v11 v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_s'45'halt_430 -> coe C_s'45'halt_430
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws._.iter-ret
d_iter'45'ret_578 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> T_RelS_378) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny -> T_RelSB_386
d_iter'45'ret_578 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 ~v11 v12
                  v13 v14
  = du_iter'45'ret_578 v6 v7 v8 v9 v12 v13 v14
du_iter'45'ret_578 ::
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> T_RelS_378) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny -> T_RelSB_386
du_iter'45'ret_578 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
        -> case coe v5 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
               -> coe C_s'45'ret_406 (coe v2 v7 v8 v6)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
               -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
        -> case coe v5 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
               -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
               -> coe
                    C_s'45'next_412
                    (coe
                       du_RelS'45'iterRun_566 (coe v0) (coe v1) (coe v2) (coe v3)
                       (coe v0 v7) (coe v1 v8) (coe v3 v7 v8 v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws._.RelS-iter∞
d_RelS'45'iter'8734'_622 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> T_RelS_378) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> AgdaAny -> AgdaAny -> T_RelS_378
d_RelS'45'iter'8734'_622 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10
                         ~v11 v12 v13 v14
  = du_RelS'45'iter'8734'_622 v6 v7 v8 v9 v12 v13 v14
du_RelS'45'iter'8734'_622 ::
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> T_RelS_378) ->
  AgdaAny -> AgdaAny -> AgdaAny -> T_RelS_378
du_RelS'45'iter'8734'_622 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_RelS'45'iterRun_566 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v0 v4) (coe v1 v5) (coe v3 v4 v5 v6)
-- Once.Denotation.TraceMonadInfLaws._.RelS-loop
d_RelS'45'loop_674 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> T_RelS_378) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> AgdaAny -> AgdaAny -> T_RelS_378
d_RelS'45'loop_674 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 ~v11
                   v12 v13 v14
  = du_RelS'45'loop_674 v6 v7 v8 v9 v12 v13 v14
du_RelS'45'loop_674 ::
  (AgdaAny -> MAlonzo.Code.Once.Internal.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> T_RelS_378) ->
  AgdaAny -> AgdaAny -> AgdaAny -> T_RelS_378
du_RelS'45'loop_674 v0 v1 v2 v3 v4 v5 v6
  = coe
      C_constructor_398
      (coe
         du_RelSB'45'loopBlock_680 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v0 v4)
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v1 v5))
         (coe d_forceS_396 (coe v3 v4 v5 v6)))
-- Once.Denotation.TraceMonadInfLaws._.RelSB-loopBlock
d_RelSB'45'loopBlock_680 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> T_RelS_378) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  T_RelSB_386 -> T_RelSB_386
d_RelSB'45'loopBlock_680 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10
                         ~v11 v12 v13 v14
  = du_RelSB'45'loopBlock_680 v6 v7 v8 v9 v12 v13 v14
du_RelSB'45'loopBlock_680 ::
  (AgdaAny -> MAlonzo.Code.Once.Internal.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> T_RelS_378) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  T_RelSB_386 -> T_RelSB_386
du_RelSB'45'loopBlock_680 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      MAlonzo.Code.Once.Internal.Trace.C_ret_114 v7
        -> case coe v6 of
             C_s'45'ret_406 v10
               -> case coe v5 of
                    MAlonzo.Code.Once.Internal.Trace.C_ret_114 v11
                      -> case coe v11 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                             -> coe
                                  du_loop'45'ret_686 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7)
                                  (coe v12) (coe v10)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Trace.C_call_118 v7 v8 v9
        -> case coe v6 of
             C_s'45'call_424 v14
               -> case coe v5 of
                    MAlonzo.Code.Once.Internal.Trace.C_call_118 v15 v16 v17
                      -> coe
                           C_s'45'call_424
                           (\ v18 ->
                              coe
                                du_RelSB'45'loopBlock_680 (coe v0) (coe v1) (coe v2) (coe v3)
                                (coe v9 v18) (coe v17 v18) (coe v14 v18))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Trace.C_halt_122 v7 v8
        -> coe seq (coe v6) (coe C_s'45'halt_430)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws._.loop-ret
d_loop'45'ret_686 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> T_RelS_378) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny -> T_RelSB_386
d_loop'45'ret_686 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 ~v11 v12
                  v13 v14
  = du_loop'45'ret_686 v6 v7 v8 v9 v12 v13 v14
du_loop'45'ret_686 ::
  (AgdaAny -> MAlonzo.Code.Once.Internal.Trace.T_T_110) ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> T_RelS_378) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny -> T_RelSB_386
du_loop'45'ret_686 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
        -> case coe v5 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
               -> coe C_s'45'ret_406 (coe v2 v7 v8 v6)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
               -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
        -> case coe v5 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
               -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
               -> coe
                    C_s'45'next_412
                    (coe
                       du_RelS'45'loop_674 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7)
                       (coe v8) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws.RelSB-embed
d_RelSB'45'embed_746 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_RelT'8242'_542 -> T_RelSB_386
d_RelSB'45'embed_746 ~v0 ~v1 ~v2 v3 v4 v5
  = du_RelSB'45'embed_746 v3 v4 v5
du_RelSB'45'embed_746 ::
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_RelT'8242'_542 -> T_RelSB_386
du_RelSB'45'embed_746 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Internal.Trace.C_rel'45'ret_554 v5
        -> coe C_s'45'ret_406 v5
      MAlonzo.Code.Once.Internal.Trace.C_rel'45'call_566 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Trace.C_call_118 v8 v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Trace.C_call_118 v11 v12 v13
                      -> coe
                           C_s'45'call_424
                           (\ v14 ->
                              coe du_RelSB'45'embed_746 (coe v10 v14) (coe v13 v14) (coe v7 v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Trace.C_rel'45'halt_572
        -> coe C_s'45'halt_430
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws.RelS-embed
d_RelS'45'embed_764 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_RelT'8242'_542 -> T_RelS_378
d_RelS'45'embed_764 ~v0 ~v1 ~v2 v3 v4 v5
  = du_RelS'45'embed_764 v3 v4 v5
du_RelS'45'embed_764 ::
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_RelT'8242'_542 -> T_RelS_378
du_RelS'45'embed_764 v0 v1 v2
  = coe
      C_constructor_398
      (coe du_RelSB'45'embed_746 (coe v0) (coe v1) (coe v2))
-- Once.Denotation.TraceMonadInfLaws.RelSB-≈ˡ
d_RelSB'45''8776''737'_780 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Iterative.T_BlockEq_266 ->
  T_RelSB_386 -> T_RelSB_386
d_RelSB'45''8776''737'_780 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_RelSB'45''8776''737'_780 v3 v4 v5 v6 v7
du_RelSB'45''8776''737'_780 ::
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Iterative.T_BlockEq_266 ->
  T_RelSB_386 -> T_RelSB_386
du_RelSB'45''8776''737'_780 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Internal.Iterative.C_ret'8776'_276 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v8
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Trace.C_ret_114 v9
                      -> case coe v7 of
                           MAlonzo.Code.Once.Internal.Iterative.C_done'8776'_318 v12
                             -> case coe v4 of
                                  C_s'45'ret_406 v15 -> coe C_s'45'ret_406 v15
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Internal.Iterative.C_next'8776'_324 v12
                             -> case coe v8 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
                                    -> case coe v9 of
                                         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v14
                                           -> case coe v4 of
                                                C_s'45'next_412 v17
                                                  -> case coe v2 of
                                                       MAlonzo.Code.Once.Internal.Trace.C_ret_114 v18
                                                         -> case coe v18 of
                                                              MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v19
                                                                -> coe
                                                                     C_s'45'next_412
                                                                     (coe
                                                                        du_RelS'45''8776''737'_794
                                                                        (coe v13) (coe v14)
                                                                        (coe v19) (coe v12)
                                                                        (coe v17))
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Iterative.C_call'8776'_288 v9
        -> case coe v0 of
             MAlonzo.Code.Once.Internal.Trace.C_call_118 v10 v11 v12
               -> case coe v1 of
                    MAlonzo.Code.Once.Internal.Trace.C_call_118 v13 v14 v15
                      -> case coe v4 of
                           C_s'45'call_424 v20
                             -> case coe v2 of
                                  MAlonzo.Code.Once.Internal.Trace.C_call_118 v21 v22 v23
                                    -> coe
                                         C_s'45'call_424
                                         (\ v24 ->
                                            coe
                                              du_RelSB'45''8776''737'_780 (coe v12 v24)
                                              (coe v15 v24) (coe v23 v24) (coe v9 v24)
                                              (coe v20 v24))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Iterative.C_halt'8776'_294
        -> coe seq (coe v4) (coe C_s'45'halt_430)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws.RelS-≈ˡ
d_RelS'45''8776''737'_794 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_TreeEq'8734'_334 ->
  T_RelS_378 -> T_RelS_378
d_RelS'45''8776''737'_794 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_RelS'45''8776''737'_794 v3 v4 v5 v6 v7
du_RelS'45''8776''737'_794 ::
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_TreeEq'8734'_334 ->
  T_RelS_378 -> T_RelS_378
du_RelS'45''8776''737'_794 v0 v1 v2 v3 v4
  = coe
      C_constructor_398
      (coe
         du_RelSB'45''8776''737'_780
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v0))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v1))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v2))
         (coe
            MAlonzo.Code.Once.Internal.Iterative.d_force'8776'_346 (coe v3))
         (coe d_forceS_396 (coe v4)))
-- Once.Denotation.TraceMonadInfLaws.RelSB-≈ʳ
d_RelSB'45''8776''691'_824 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Iterative.T_BlockEq_266 ->
  T_RelSB_386 -> T_RelSB_386
d_RelSB'45''8776''691'_824 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_RelSB'45''8776''691'_824 v3 v4 v5 v6 v7
du_RelSB'45''8776''691'_824 ::
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Iterative.T_BlockEq_266 ->
  T_RelSB_386 -> T_RelSB_386
du_RelSB'45''8776''691'_824 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Internal.Iterative.C_ret'8776'_276 v7
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Trace.C_ret_114 v8
               -> case coe v2 of
                    MAlonzo.Code.Once.Internal.Trace.C_ret_114 v9
                      -> case coe v7 of
                           MAlonzo.Code.Once.Internal.Iterative.C_done'8776'_318 v12
                             -> case coe v4 of
                                  C_s'45'ret_406 v15 -> coe C_s'45'ret_406 v15
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Internal.Iterative.C_next'8776'_324 v12
                             -> case coe v8 of
                                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
                                    -> case coe v9 of
                                         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v14
                                           -> case coe v4 of
                                                C_s'45'next_412 v17
                                                  -> case coe v0 of
                                                       MAlonzo.Code.Once.Internal.Trace.C_ret_114 v18
                                                         -> case coe v18 of
                                                              MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v19
                                                                -> coe
                                                                     C_s'45'next_412
                                                                     (coe
                                                                        du_RelS'45''8776''691'_838
                                                                        (coe v19) (coe v13)
                                                                        (coe v14) (coe v12)
                                                                        (coe v17))
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Iterative.C_call'8776'_288 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Internal.Trace.C_call_118 v10 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Internal.Trace.C_call_118 v13 v14 v15
                      -> case coe v4 of
                           C_s'45'call_424 v20
                             -> case coe v0 of
                                  MAlonzo.Code.Once.Internal.Trace.C_call_118 v21 v22 v23
                                    -> coe
                                         C_s'45'call_424
                                         (\ v24 ->
                                            coe
                                              du_RelSB'45''8776''691'_824 (coe v23 v24)
                                              (coe v12 v24) (coe v15 v24) (coe v9 v24)
                                              (coe v20 v24))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Iterative.C_halt'8776'_294
        -> coe seq (coe v4) (coe C_s'45'halt_430)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws.RelS-≈ʳ
d_RelS'45''8776''691'_838 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_TreeEq'8734'_334 ->
  T_RelS_378 -> T_RelS_378
d_RelS'45''8776''691'_838 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_RelS'45''8776''691'_838 v3 v4 v5 v6 v7
du_RelS'45''8776''691'_838 ::
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_TreeEq'8734'_334 ->
  T_RelS_378 -> T_RelS_378
du_RelS'45''8776''691'_838 v0 v1 v2 v3 v4
  = coe
      C_constructor_398
      (coe
         du_RelSB'45''8776''691'_824
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v0))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v1))
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v2))
         (coe
            MAlonzo.Code.Once.Internal.Iterative.d_force'8776'_346 (coe v3))
         (coe d_forceS_396 (coe v4)))
-- Once.Denotation.TraceMonadInfLaws.embed-bindB
d_embed'45'bindB_866 ::
  () ->
  () ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Trace.T_T_110) ->
  MAlonzo.Code.Once.Internal.Iterative.T_BlockEq_266
d_embed'45'bindB_866 ~v0 ~v1 v2 v3 = du_embed'45'bindB_866 v2 v3
du_embed'45'bindB_866 ::
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Trace.T_T_110) ->
  MAlonzo.Code.Once.Internal.Iterative.T_BlockEq_266
du_embed'45'bindB_866 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Trace.C_ret_114 v2
        -> coe
             du_'8776''8734''45'reflB_24 erased
             (coe
                MAlonzo.Code.Once.Internal.Iterative.du_embedBlock_118 (coe v1 v2))
      MAlonzo.Code.Once.Internal.Trace.C_call_118 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Internal.Iterative.C_call'8776'_288
             (\ v5 -> coe du_embed'45'bindB_866 (coe v4 v5) (coe v1))
      MAlonzo.Code.Once.Internal.Trace.C_halt_122 v2 v3
        -> coe MAlonzo.Code.Once.Internal.Iterative.C_halt'8776'_294
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws.embed-bind
d_embed'45'bind_900 ::
  () ->
  () ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Trace.T_T_110) ->
  MAlonzo.Code.Once.Internal.Iterative.T_TreeEq'8734'_334
d_embed'45'bind_900 ~v0 ~v1 v2 v3 = du_embed'45'bind_900 v2 v3
du_embed'45'bind_900 ::
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Trace.T_T_110) ->
  MAlonzo.Code.Once.Internal.Iterative.T_TreeEq'8734'_334
du_embed'45'bind_900 v0 v1
  = coe
      MAlonzo.Code.Once.Internal.Iterative.C_constructor_348
      (coe du_embed'45'bindB_866 (coe v0) (coe v1))
