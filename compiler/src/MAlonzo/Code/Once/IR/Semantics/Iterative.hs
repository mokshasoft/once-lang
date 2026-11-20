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

module MAlonzo.Code.Once.IR.Semantics.Iterative where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.IR.Semantics.Trace
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.IR.Semantics.Iterative.T∞
d_T'8734'_10 a0 = ()
data T_T'8734'_10
  = C_constructor_18 MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
-- Once.IR.Semantics.Iterative.T∞.force
d_force_16 ::
  T_T'8734'_10 -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
d_force_16 v0
  = case coe v0 of
      C_constructor_18 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Iterative.return∞
d_return'8734'_22 :: () -> AgdaAny -> T_T'8734'_10
d_return'8734'_22 ~v0 v1 = du_return'8734'_22 v1
du_return'8734'_22 :: AgdaAny -> T_T'8734'_10
du_return'8734'_22 v0
  = coe
      C_constructor_18
      (coe
         MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116
         (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v0)))
-- Once.IR.Semantics.Iterative._>>=∞_
d__'62''62''61''8734'__30 ::
  () ->
  () -> T_T'8734'_10 -> (AgdaAny -> T_T'8734'_10) -> T_T'8734'_10
d__'62''62''61''8734'__30 ~v0 ~v1 v2 v3
  = du__'62''62''61''8734'__30 v2 v3
du__'62''62''61''8734'__30 ::
  T_T'8734'_10 -> (AgdaAny -> T_T'8734'_10) -> T_T'8734'_10
du__'62''62''61''8734'__30 v0 v1
  = coe
      C_constructor_18
      (coe du_bindBlock_36 (coe d_force_16 (coe v0)) (coe v1))
-- Once.IR.Semantics.Iterative.bindBlock
d_bindBlock_36 ::
  () ->
  () ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  (AgdaAny -> T_T'8734'_10) ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
d_bindBlock_36 ~v0 ~v1 v2 v3 = du_bindBlock_36 v2 v3
du_bindBlock_36 ::
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  (AgdaAny -> T_T'8734'_10) ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
du_bindBlock_36 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116 v2
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
               -> coe d_force_16 (coe v1 v3)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
               -> coe
                    MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe du__'62''62''61''8734'__30 (coe v3) (coe v1)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.Semantics.Trace.C_call_120 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.IR.Semantics.Trace.C_call_120 (coe v2) (coe v3)
             (coe (\ v5 -> coe du_bindBlock_36 (coe v4 v5) (coe v1)))
      MAlonzo.Code.Once.IR.Semantics.Trace.C_halt_124 v2 v3 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Iterative.embedBlock
d_embedBlock_70 ::
  () ->
  () ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
d_embedBlock_70 ~v0 ~v1 v2 = du_embedBlock_70 v2
du_embedBlock_70 ::
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
du_embedBlock_70 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116 v1
        -> coe
             MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116
             (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v1))
      MAlonzo.Code.Once.IR.Semantics.Trace.C_call_120 v1 v2 v3
        -> coe
             MAlonzo.Code.Once.IR.Semantics.Trace.C_call_120 (coe v1) (coe v2)
             (coe (\ v4 -> coe du_embedBlock_70 (coe v3 v4)))
      MAlonzo.Code.Once.IR.Semantics.Trace.C_halt_124 v1 v2 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Iterative.embed
d_embed_88 ::
  () -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 -> T_T'8734'_10
d_embed_88 ~v0 v1 = du_embed_88 v1
du_embed_88 ::
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 -> T_T'8734'_10
du_embed_88 v0
  = coe C_constructor_18 (coe du_embedBlock_70 (coe v0))
-- Once.IR.Semantics.Iterative.loop
d_loop_96 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112) ->
  AgdaAny -> T_T'8734'_10
d_loop_96 ~v0 ~v1 v2 v3 = du_loop_96 v2 v3
du_loop_96 ::
  (AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112) ->
  AgdaAny -> T_T'8734'_10
du_loop_96 v0 v1
  = coe C_constructor_18 (coe du_loopBlock_102 (coe v0) (coe v0 v1))
-- Once.IR.Semantics.Iterative.loopBlock
d_loopBlock_102 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112) ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
d_loopBlock_102 ~v0 ~v1 v2 v3 = du_loopBlock_102 v2 v3
du_loopBlock_102 ::
  (AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112) ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
du_loopBlock_102 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116 v2
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> coe v1
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
               -> coe
                    MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe du_loop_96 (coe v0) (coe v3)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.Semantics.Trace.C_call_120 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.IR.Semantics.Trace.C_call_120 (coe v2) (coe v3)
             (coe (\ v5 -> coe du_loopBlock_102 (coe v0) (coe v4 v5)))
      MAlonzo.Code.Once.IR.Semantics.Trace.C_halt_124 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Iterative.NowB
d_NowB_134 ::
  () -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 -> ()
d_NowB_134 = erased
-- Once.IR.Semantics.Iterative.nowB
d_nowB_140 ::
  () ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 -> AgdaAny -> AgdaAny
d_nowB_140 ~v0 v1 ~v2 = du_nowB_140 v1
du_nowB_140 ::
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 -> AgdaAny
du_nowB_140 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116 v1
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> coe v2
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Iterative.Now
d_Now_146 :: () -> T_T'8734'_10 -> ()
d_Now_146 = erased
-- Once.IR.Semantics.Iterative.valueNow
d_valueNow_154 :: () -> T_T'8734'_10 -> AgdaAny -> AgdaAny
d_valueNow_154 ~v0 v1 ~v2 = du_valueNow_154 v1
du_valueNow_154 :: T_T'8734'_10 -> AgdaAny
du_valueNow_154 v0 = coe du_nowB_140 (coe d_force_16 (coe v0))
-- Once.IR.Semantics.Iterative.iterRun
d_iterRun_164 ::
  () ->
  () -> (AgdaAny -> T_T'8734'_10) -> T_T'8734'_10 -> T_T'8734'_10
d_iterRun_164 ~v0 ~v1 v2 v3 = du_iterRun_164 v2 v3
du_iterRun_164 ::
  (AgdaAny -> T_T'8734'_10) -> T_T'8734'_10 -> T_T'8734'_10
du_iterRun_164 v0 v1
  = coe
      C_constructor_18
      (coe du_iterBlock_170 (coe v0) (coe d_force_16 (coe v1)))
-- Once.IR.Semantics.Iterative.iterBlock
d_iterBlock_170 ::
  () ->
  () ->
  (AgdaAny -> T_T'8734'_10) ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
d_iterBlock_170 ~v0 ~v1 v2 v3 = du_iterBlock_170 v2 v3
du_iterBlock_170 ::
  (AgdaAny -> T_T'8734'_10) ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
du_iterBlock_170 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116 v2
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
                      -> coe MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116 (coe v3)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
                      -> coe
                           MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116
                           (coe
                              MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                              (coe du_iterRun_164 (coe v0) (coe v0 v4)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
               -> coe
                    MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe du_iterRun_164 (coe v0) (coe v3)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.Semantics.Trace.C_call_120 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.IR.Semantics.Trace.C_call_120 (coe v2) (coe v3)
             (coe (\ v5 -> coe du_iterBlock_170 (coe v0) (coe v4 v5)))
      MAlonzo.Code.Once.IR.Semantics.Trace.C_halt_124 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Iterative.iter∞
d_iter'8734'_208 ::
  () -> () -> (AgdaAny -> T_T'8734'_10) -> AgdaAny -> T_T'8734'_10
d_iter'8734'_208 ~v0 ~v1 v2 v3 = du_iter'8734'_208 v2 v3
du_iter'8734'_208 ::
  (AgdaAny -> T_T'8734'_10) -> AgdaAny -> T_T'8734'_10
du_iter'8734'_208 v0 v1 = coe du_iterRun_164 (coe v0) (coe v0 v1)
-- Once.IR.Semantics.Iterative.BlockEq
d_BlockEq_218 a0 a1 a2 a3 = ()
data T_BlockEq_218
  = C_ret'8776'_228 AgdaAny |
    C_call'8776'_240 (AgdaAny -> T_BlockEq_218) | C_halt'8776'_246
-- Once.IR.Semantics.Iterative.StepEq
d_StepEq_256 a0 a1 a2 a3 a4 a5 = ()
data T_StepEq_256
  = C_done'8776'_270 AgdaAny | C_next'8776'_276 AgdaAny
-- Once.IR.Semantics.Iterative.TreeEq∞
d_TreeEq'8734'_286 a0 a1 a2 a3 = ()
data T_TreeEq'8734'_286 = C_constructor_300 T_BlockEq_218
-- Once.IR.Semantics.Iterative.TreeEq∞.force≈
d_force'8776'_298 :: T_TreeEq'8734'_286 -> T_BlockEq_218
d_force'8776'_298 v0
  = case coe v0 of
      C_constructor_300 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Iterative._.⟦_⟧F
d_'10214'_'10215'F_304 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> ()
d_'10214'_'10215'F_304 = erased
-- Once.IR.Semantics.Iterative.fmap∞
d_fmap'8734'_310 ::
  () -> () -> (AgdaAny -> AgdaAny) -> T_T'8734'_10 -> T_T'8734'_10
d_fmap'8734'_310 ~v0 ~v1 v2 v3 = du_fmap'8734'_310 v2 v3
du_fmap'8734'_310 ::
  (AgdaAny -> AgdaAny) -> T_T'8734'_10 -> T_T'8734'_10
du_fmap'8734'_310 v0 v1
  = coe
      du__'62''62''61''8734'__30 (coe v1)
      (coe (\ v2 -> coe du_return'8734'_22 (coe v0 v2)))
-- Once.IR.Semantics.Iterative.seqF∞
d_seqF'8734'_324 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () -> AgdaAny -> T_T'8734'_10
d_seqF'8734'_324 ~v0 v1 ~v2 v3 = du_seqF'8734'_324 v1 v3
du_seqF'8734'_324 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> AgdaAny -> T_T'8734'_10
du_seqF'8734'_324 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_K_38 v2
        -> coe du_return'8734'_22 (coe v1)
      MAlonzo.Code.Once.Spec.Type.C_Id_40 -> coe v1
      MAlonzo.Code.Once.Spec.Type.C__'8853'__42 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    du_fmap'8734'_310 (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
                    (coe du_seqF'8734'_324 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    du_fmap'8734'_310 (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
                    (coe du_seqF'8734'_324 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C__'8855'__44 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    du__'62''62''61''8734'__30
                    (coe du_seqF'8734'_324 (coe v2) (coe v4))
                    (coe
                       (\ v6 ->
                          coe
                            du__'62''62''61''8734'__30
                            (coe du_seqF'8734'_324 (coe v3) (coe v5))
                            (coe
                               (\ v7 ->
                                  coe
                                    du_return'8734'_22
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                       (coe v7))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
