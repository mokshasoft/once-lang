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
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Lang.Equivalence
import qualified MAlonzo.Code.Once.Lang.Event
import qualified MAlonzo.Code.Once.Lang.Iterative
import qualified MAlonzo.Code.Once.Lang.Trace

-- Once.Denotation.TraceMonadInfLaws.≈∞-refl
d_'8776''8734''45'refl_14 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202
d_'8776''8734''45'refl_14 ~v0 ~v1 v2 v3
  = du_'8776''8734''45'refl_14 v2 v3
du_'8776''8734''45'refl_14 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202
du_'8776''8734''45'refl_14 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Iterative.C_constructor_216
      (coe
         du_'8776''8734''45'reflF_24 (coe v0)
         (coe MAlonzo.Code.Once.Lang.Iterative.d_force_84 (coe v1)))
-- Once.Denotation.TraceMonadInfLaws.≈∞-reflF
d_'8776''8734''45'reflF_24 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158
d_'8776''8734''45'reflF_24 ~v0 ~v1 v2 v3
  = du_'8776''8734''45'reflF_24 v2 v3
du_'8776''8734''45'reflF_24 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158
du_'8776''8734''45'reflF_24 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Iterative.C_ret'8734'_66 v2
        -> coe
             MAlonzo.Code.Once.Lang.Iterative.C_ret'8776''8734'_174 (coe v0 v2)
      MAlonzo.Code.Once.Lang.Iterative.C_call'8734'_70 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Iterative.C_call'8776''8734'_186
             (\ v5 -> coe du_'8776''8734''45'refl_14 (coe v0) (coe v4 v5))
      MAlonzo.Code.Once.Lang.Iterative.C_halt'8734'_74 v2 v3
        -> coe MAlonzo.Code.Once.Lang.Iterative.C_halt'8776''8734'_192
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws.≈∞-bind
d_'8776''8734''45'bind_70 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202) ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202
d_'8776''8734''45'bind_70 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_'8776''8734''45'bind_70 v4 v5 v6 v7 v8 v9
du_'8776''8734''45'bind_70 ::
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202) ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202
du_'8776''8734''45'bind_70 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Lang.Iterative.C_constructor_216
      (coe
         du_'8776''8734''45'bindF_92
         (coe MAlonzo.Code.Once.Lang.Iterative.d_force_84 (coe v0))
         (coe MAlonzo.Code.Once.Lang.Iterative.d_force_84 (coe v1)) (coe v2)
         (coe v3)
         (coe MAlonzo.Code.Once.Lang.Iterative.d_force'8776'_214 (coe v4))
         (coe v5))
-- Once.Denotation.TraceMonadInfLaws.≈∞-bindF
d_'8776''8734''45'bindF_92 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202) ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158
d_'8776''8734''45'bindF_92 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_'8776''8734''45'bindF_92 v4 v5 v6 v7 v8 v9
du_'8776''8734''45'bindF_92 ::
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202) ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158
du_'8776''8734''45'bindF_92 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Once.Lang.Iterative.C_ret'8776''8734'_174 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Iterative.C_ret'8734'_66 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Iterative.C_ret'8734'_66 v10
                      -> coe
                           MAlonzo.Code.Once.Lang.Iterative.d_force'8776'_214
                           (coe v5 v9 v10 v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Iterative.C_call'8776''8734'_186 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Iterative.C_call'8734'_70 v11 v12 v13
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Iterative.C_call'8734'_70 v14 v15 v16
                      -> coe
                           MAlonzo.Code.Once.Lang.Iterative.C_call'8776''8734'_186
                           (\ v17 ->
                              coe
                                du_'8776''8734''45'bind_70 (coe v13 v17) (coe v16 v17) (coe v2)
                                (coe v3) (coe v10 v17) (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Iterative.C_halt'8776''8734'_192
        -> coe MAlonzo.Code.Once.Lang.Iterative.C_halt'8776''8734'_192
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws.embed-≈
d_embed'45''8776'_118 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Equivalence.T_TreeEq_10 ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202
d_embed'45''8776'_118 ~v0 ~v1 v2 v3 v4
  = du_embed'45''8776'_118 v2 v3 v4
du_embed'45''8776'_118 ::
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Equivalence.T_TreeEq_10 ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202
du_embed'45''8776'_118 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Iterative.C_constructor_216
      (case coe v2 of
         MAlonzo.Code.Once.Lang.Equivalence.C_ret'8776'_20 v5
           -> coe MAlonzo.Code.Once.Lang.Iterative.C_ret'8776''8734'_174 v5
         MAlonzo.Code.Once.Lang.Equivalence.C_call'8776'_32 v7
           -> case coe v0 of
                MAlonzo.Code.Once.Lang.Trace.C_call_118 v8 v9 v10
                  -> case coe v1 of
                       MAlonzo.Code.Once.Lang.Trace.C_call_118 v11 v12 v13
                         -> coe
                              MAlonzo.Code.Once.Lang.Iterative.C_call'8776''8734'_186
                              (\ v14 ->
                                 coe
                                   du_embed'45''8776'_118 (coe v10 v14) (coe v13 v14) (coe v7 v14))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.Lang.Equivalence.C_halt'8776'_38
           -> coe MAlonzo.Code.Once.Lang.Iterative.C_halt'8776''8734'_192
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Denotation.TraceMonadInfLaws.embed-bind
d_embed'45'bind_136 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202
d_embed'45'bind_136 ~v0 ~v1 v2 v3 = du_embed'45'bind_136 v2 v3
du_embed'45'bind_136 ::
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202
du_embed'45'bind_136 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Iterative.C_constructor_216
      (case coe v0 of
         MAlonzo.Code.Once.Lang.Trace.C_ret_114 v2
           -> coe
                du_'8776''8734''45'reflF_24 erased
                (coe
                   MAlonzo.Code.Once.Lang.Iterative.d_force_84
                   (coe MAlonzo.Code.Once.Lang.Iterative.du_embed_132 (coe v1 v2)))
         MAlonzo.Code.Once.Lang.Trace.C_call_118 v2 v3 v4
           -> coe
                MAlonzo.Code.Once.Lang.Iterative.C_call'8776''8734'_186
                (\ v5 -> coe du_embed'45'bind_136 (coe v4 v5) (coe v1))
         MAlonzo.Code.Once.Lang.Trace.C_halt_122 v2 v3
           -> coe MAlonzo.Code.Once.Lang.Iterative.C_halt'8776''8734'_192
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Denotation.TraceMonadInfLaws.events∞-embed
d_events'8734''45'embed_170 ::
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_events'8734''45'embed_170 = erased
-- Once.Denotation.TraceMonadInfLaws.events∞-call
d_events'8734''45'call_190 ::
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Trace.T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  Maybe AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_events'8734''45'call_190 = erased
-- Once.Denotation.TraceMonadInfLaws.≈∞-sym
d_'8776''8734''45'sym_280 ::
  () ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202 ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202
d_'8776''8734''45'sym_280 ~v0 v1 v2 v3
  = du_'8776''8734''45'sym_280 v1 v2 v3
du_'8776''8734''45'sym_280 ::
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202 ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202
du_'8776''8734''45'sym_280 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Iterative.C_constructor_216
      (coe
         du_'8776''8734''45'symF_288
         (coe MAlonzo.Code.Once.Lang.Iterative.d_force_84 (coe v0))
         (coe MAlonzo.Code.Once.Lang.Iterative.d_force_84 (coe v1))
         (coe MAlonzo.Code.Once.Lang.Iterative.d_force'8776'_214 (coe v2)))
-- Once.Denotation.TraceMonadInfLaws.≈∞-symF
d_'8776''8734''45'symF_288 ::
  () ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158 ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158
d_'8776''8734''45'symF_288 ~v0 v1 v2 v3
  = du_'8776''8734''45'symF_288 v1 v2 v3
du_'8776''8734''45'symF_288 ::
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158 ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158
du_'8776''8734''45'symF_288 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Iterative.C_ret'8776''8734'_174 v5
        -> coe
             MAlonzo.Code.Once.Lang.Iterative.C_ret'8776''8734'_174 erased
      MAlonzo.Code.Once.Lang.Iterative.C_call'8776''8734'_186 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Iterative.C_call'8734'_70 v8 v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Iterative.C_call'8734'_70 v11 v12 v13
                      -> coe
                           MAlonzo.Code.Once.Lang.Iterative.C_call'8776''8734'_186
                           (\ v14 ->
                              coe
                                du_'8776''8734''45'sym_280 (coe v10 v14) (coe v13 v14)
                                (coe v7 v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Iterative.C_halt'8776''8734'_192
        -> coe MAlonzo.Code.Once.Lang.Iterative.C_halt'8776''8734'_192
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws.≈∞-rewrite
d_'8776''8734''45'rewrite_308 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202 ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202 ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202 ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202
d_'8776''8734''45'rewrite_308 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8
  = du_'8776''8734''45'rewrite_308 v2 v3 v4 v5 v6 v7 v8
du_'8776''8734''45'rewrite_308 ::
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202 ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202 ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202 ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202
du_'8776''8734''45'rewrite_308 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Lang.Iterative.C_constructor_216
      (coe
         du_'8776''8734''45'rewriteF_322
         (coe MAlonzo.Code.Once.Lang.Iterative.d_force_84 (coe v0))
         (coe MAlonzo.Code.Once.Lang.Iterative.d_force_84 (coe v1))
         (coe MAlonzo.Code.Once.Lang.Iterative.d_force_84 (coe v2))
         (coe MAlonzo.Code.Once.Lang.Iterative.d_force_84 (coe v3))
         (coe MAlonzo.Code.Once.Lang.Iterative.d_force'8776'_214 (coe v4))
         (coe MAlonzo.Code.Once.Lang.Iterative.d_force'8776'_214 (coe v5))
         (coe MAlonzo.Code.Once.Lang.Iterative.d_force'8776'_214 (coe v6)))
-- Once.Denotation.TraceMonadInfLaws.≈∞-rewriteF
d_'8776''8734''45'rewriteF_322 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158 ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158 ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158 ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158
d_'8776''8734''45'rewriteF_322 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8
  = du_'8776''8734''45'rewriteF_322 v2 v3 v4 v5 v6 v7 v8
du_'8776''8734''45'rewriteF_322 ::
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158 ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158 ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158 ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158
du_'8776''8734''45'rewriteF_322 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      MAlonzo.Code.Once.Lang.Iterative.C_ret'8776''8734'_174 v9
        -> coe
             seq (coe v5)
             (case coe v6 of
                MAlonzo.Code.Once.Lang.Iterative.C_ret'8776''8734'_174 v12
                  -> coe MAlonzo.Code.Once.Lang.Iterative.C_ret'8776''8734'_174 v12
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Lang.Iterative.C_call'8776''8734'_186 v11
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Iterative.C_call'8734'_70 v12 v13 v14
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Iterative.C_call'8734'_70 v15 v16 v17
                      -> case coe v5 of
                           MAlonzo.Code.Once.Lang.Iterative.C_call'8776''8734'_186 v22
                             -> case coe v2 of
                                  MAlonzo.Code.Once.Lang.Iterative.C_call'8734'_70 v23 v24 v25
                                    -> case coe v3 of
                                         MAlonzo.Code.Once.Lang.Iterative.C_call'8734'_70 v26 v27 v28
                                           -> case coe v6 of
                                                MAlonzo.Code.Once.Lang.Iterative.C_call'8776''8734'_186 v33
                                                  -> coe
                                                       MAlonzo.Code.Once.Lang.Iterative.C_call'8776''8734'_186
                                                       (\ v34 ->
                                                          coe
                                                            du_'8776''8734''45'rewrite_308
                                                            (coe v14 v34) (coe v17 v34)
                                                            (coe v25 v34) (coe v28 v34)
                                                            (coe v11 v34) (coe v22 v34)
                                                            (coe v33 v34))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Iterative.C_halt'8776''8734'_192
        -> coe
             seq (coe v5)
             (coe
                seq (coe v6)
                (coe MAlonzo.Code.Once.Lang.Iterative.C_halt'8776''8734'_192))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws.≈∞-map
d_'8776''8734''45'map_354 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202 ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202
d_'8776''8734''45'map_354 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_'8776''8734''45'map_354 v3 v4 v5 v6
du_'8776''8734''45'map_354 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202 ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202
du_'8776''8734''45'map_354 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Iterative.C_constructor_216
      (coe
         du_'8776''8734''45'mapF_370 (coe v0)
         (coe MAlonzo.Code.Once.Lang.Iterative.d_force_84 (coe v1))
         (coe MAlonzo.Code.Once.Lang.Iterative.d_force_84 (coe v2))
         (coe MAlonzo.Code.Once.Lang.Iterative.d_force'8776'_214 (coe v3)))
-- Once.Denotation.TraceMonadInfLaws.≈∞-mapF
d_'8776''8734''45'mapF_370 ::
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158 ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158
d_'8776''8734''45'mapF_370 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_'8776''8734''45'mapF_370 v3 v4 v5 v6
du_'8776''8734''45'mapF_370 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158 ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158
du_'8776''8734''45'mapF_370 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Lang.Iterative.C_ret'8776''8734'_174 v6
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Iterative.C_ret'8734'_66 v7
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Iterative.C_ret'8734'_66 v8
                      -> coe
                           MAlonzo.Code.Once.Lang.Iterative.C_ret'8776''8734'_174
                           (coe v0 v7 v8 v6)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Iterative.C_call'8776''8734'_186 v8
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Iterative.C_call'8734'_70 v9 v10 v11
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Iterative.C_call'8734'_70 v12 v13 v14
                      -> coe
                           MAlonzo.Code.Once.Lang.Iterative.C_call'8776''8734'_186
                           (\ v15 ->
                              coe
                                du_'8776''8734''45'map_354 (coe v0) (coe v11 v15) (coe v14 v15)
                                (coe v8 v15))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Iterative.C_halt'8776''8734'_192
        -> coe MAlonzo.Code.Once.Lang.Iterative.C_halt'8776''8734'_192
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws.≈∞-idˡ
d_'8776''8734''45'id'737'_396 ::
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202
d_'8776''8734''45'id'737'_396 ~v0 ~v1 v2 v3
  = du_'8776''8734''45'id'737'_396 v2 v3
du_'8776''8734''45'id'737'_396 ::
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202
du_'8776''8734''45'id'737'_396 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Iterative.C_constructor_216
      (coe
         du_'8776''8734''45'reflF_24 erased
         (coe MAlonzo.Code.Once.Lang.Iterative.d_force_84 (coe v1 v0)))
-- Once.Denotation.TraceMonadInfLaws.≈∞-idʳ
d_'8776''8734''45'id'691'_408 ::
  () ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202
d_'8776''8734''45'id'691'_408 ~v0 v1
  = du_'8776''8734''45'id'691'_408 v1
du_'8776''8734''45'id'691'_408 ::
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202
du_'8776''8734''45'id'691'_408 v0
  = coe
      MAlonzo.Code.Once.Lang.Iterative.C_constructor_216
      (coe
         du_'8776''8734''45'id'691'F_414
         (coe MAlonzo.Code.Once.Lang.Iterative.d_force_84 (coe v0)))
-- Once.Denotation.TraceMonadInfLaws.≈∞-idʳF
d_'8776''8734''45'id'691'F_414 ::
  () ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158
d_'8776''8734''45'id'691'F_414 ~v0 v1
  = du_'8776''8734''45'id'691'F_414 v1
du_'8776''8734''45'id'691'F_414 ::
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158
du_'8776''8734''45'id'691'F_414 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Iterative.C_ret'8734'_66 v1
        -> coe
             MAlonzo.Code.Once.Lang.Iterative.C_ret'8776''8734'_174 erased
      MAlonzo.Code.Once.Lang.Iterative.C_call'8734'_70 v1 v2 v3
        -> coe
             MAlonzo.Code.Once.Lang.Iterative.C_call'8776''8734'_186
             (\ v4 -> coe du_'8776''8734''45'id'691'_408 (coe v3 v4))
      MAlonzo.Code.Once.Lang.Iterative.C_halt'8734'_74 v1 v2
        -> coe MAlonzo.Code.Once.Lang.Iterative.C_halt'8776''8734'_192
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws.≈∞-assoc
d_'8776''8734''45'assoc_446 ::
  () ->
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202
d_'8776''8734''45'assoc_446 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'8776''8734''45'assoc_446 v3 v4 v5
du_'8776''8734''45'assoc_446 ::
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202
du_'8776''8734''45'assoc_446 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Iterative.C_constructor_216
      (coe
         du_'8776''8734''45'assocF_462
         (coe MAlonzo.Code.Once.Lang.Iterative.d_force_84 (coe v0)) (coe v1)
         (coe v2))
-- Once.Denotation.TraceMonadInfLaws.≈∞-assocF
d_'8776''8734''45'assocF_462 ::
  () ->
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158
d_'8776''8734''45'assocF_462 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'8776''8734''45'assocF_462 v3 v4 v5
du_'8776''8734''45'assocF_462 ::
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158
du_'8776''8734''45'assocF_462 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Iterative.C_ret'8734'_66 v3
        -> coe
             du_'8776''8734''45'reflF_24 erased
             (coe
                MAlonzo.Code.Once.Lang.Iterative.du_bind'8734'F_104
                (coe MAlonzo.Code.Once.Lang.Iterative.d_force_84 (coe v1 v3))
                (coe v2))
      MAlonzo.Code.Once.Lang.Iterative.C_call'8734'_70 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Iterative.C_call'8776''8734'_186
             (\ v6 ->
                coe du_'8776''8734''45'assoc_446 (coe v5 v6) (coe v1) (coe v2))
      MAlonzo.Code.Once.Lang.Iterative.C_halt'8734'_74 v3 v4
        -> coe MAlonzo.Code.Once.Lang.Iterative.C_halt'8776''8734'_192
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws.RelT∞′
d_RelT'8734''8242'_504 a0 a1 a2 a3 a4 = ()
data T_RelT'8734''8242'_504
  = C_rel'8734''45'ret_518 AgdaAny AgdaAny |
    C_rel'8734''45'call_532 (AgdaAny ->
                             MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78)
                            (AgdaAny -> T_RelT'8734''8242'_504) |
    C_rel'8734''45'halt_540
-- Once.Denotation.TraceMonadInfLaws.RelT∞′-force
d_RelT'8734''8242''45'force_554 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_RelT'8734''8242'_504 -> T_RelT'8734''8242'_504
d_RelT'8734''8242''45'force_554 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_RelT'8734''8242''45'force_554 v7
du_RelT'8734''8242''45'force_554 ::
  T_RelT'8734''8242'_504 -> T_RelT'8734''8242'_504
du_RelT'8734''8242''45'force_554 v0 = coe v0
-- Once.Denotation.TraceMonadInfLaws.RelT∞′-bind
d_RelT'8734''8242''45'bind_596 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  T_RelT'8734''8242'_504 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> T_RelT'8734''8242'_504) ->
  T_RelT'8734''8242'_504
d_RelT'8734''8242''45'bind_596 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8
                               ~v9 v10 v11
  = du_RelT'8734''8242''45'bind_596 v7 v8 v10 v11
du_RelT'8734''8242''45'bind_596 ::
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  T_RelT'8734''8242'_504 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> T_RelT'8734''8242'_504) ->
  T_RelT'8734''8242'_504
du_RelT'8734''8242''45'bind_596 v0 v1 v2 v3
  = case coe v2 of
      C_rel'8734''45'ret_518 v5 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Trace.C_ret_114 v9 -> coe v3 v5 v9 v8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_rel'8734''45'call_532 v7 v10
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Trace.C_call_118 v11 v12 v13
               -> coe
                    C_rel'8734''45'call_532
                    (\ v14 ->
                       coe
                         MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__98
                         (coe v7 v14) (coe v1))
                    (\ v14 ->
                       coe
                         du_RelT'8734''8242''45'bind_596 (coe v13 v14) (coe v1)
                         (coe v10 v14) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_rel'8734''45'halt_540 -> coe C_rel'8734''45'halt_540
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws.ret-node
d_ret'45'node_644 ::
  () ->
  (MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
   MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 -> ()) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ret'45'node_644 = erased
-- Once.Denotation.TraceMonadInfLaws.call-node
d_call'45'node_664 ::
  () ->
  (MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
   MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 -> ()) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Trace.T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_call'45'node_664 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8
  = du_call'45'node_664 v2 v7
du_call'45'node_664 ::
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_call'45'node_664 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Iterative.C_call'8776''8734'_186 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Iterative.C_call'8734'_70 v7 v8 v9
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws.halt-node
d_halt'45'node_680 ::
  () ->
  (MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
   MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 -> ()) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Trace.T_HaltOp_76 ->
  AgdaAny ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_halt'45'node_680 = erased
-- Once.Denotation.TraceMonadInfLaws.RelT∞′-≈
d_RelT'8734''8242''45''8776'_694 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202 ->
  T_RelT'8734''8242'_504 -> T_RelT'8734''8242'_504
d_RelT'8734''8242''45''8776'_694 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7
  = du_RelT'8734''8242''45''8776'_694 v3 v5 v6 v7
du_RelT'8734''8242''45''8776'_694 ::
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202 ->
  T_RelT'8734''8242'_504 -> T_RelT'8734''8242'_504
du_RelT'8734''8242''45''8776'_694 v0 v1 v2 v3
  = case coe v3 of
      C_rel'8734''45'ret_518 v5 v8 -> coe C_rel'8734''45'ret_518 v5 v8
      C_rel'8734''45'call_532 v7 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Trace.C_call_118 v11 v12 v13
               -> coe
                    du_RelT'8734''8242''45''8776'call_718 (coe v7) (coe v13)
                    (coe
                       du_call'45'node_664
                       (coe MAlonzo.Code.Once.Lang.Iterative.d_force_84 (coe v0))
                       (coe MAlonzo.Code.Once.Lang.Iterative.d_force'8776'_214 (coe v2)))
                    (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_rel'8734''45'halt_540 -> coe C_rel'8734''45'halt_540
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws.RelT∞′-≈call
d_RelT'8734''8242''45''8776'call_718 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Trace.T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> T_RelT'8734''8242'_504) -> T_RelT'8734''8242'_504
d_RelT'8734''8242''45''8776'call_718 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
                                     v8 v9
  = du_RelT'8734''8242''45''8776'call_718 v6 v7 v8 v9
du_RelT'8734''8242''45''8776'call_718 ::
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> T_RelT'8734''8242'_504) -> T_RelT'8734''8242'_504
du_RelT'8734''8242''45''8776'call_718 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    C_rel'8734''45'call_532 v4
                    (\ v8 ->
                       coe
                         du_RelT'8734''8242''45''8776'_694 (coe v4 v8) (coe v1 v8)
                         (coe v7 v8) (coe v3 v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws.RelT∞′-events
d_RelT'8734''8242''45'events_762 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  T_RelT'8734''8242'_504 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_RelT'8734''8242''45'events_762 = erased
-- Once.Denotation.TraceMonadInfLaws.RelT∞′-events-call
d_RelT'8734''8242''45'events'45'call_788 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Trace.T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  (AgdaAny -> T_RelT'8734''8242'_504) ->
  Maybe AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_RelT'8734''8242''45'events'45'call_788 = erased
-- Once.Denotation.TraceMonadInfLaws.events∞-≈
d_events'8734''45''8776'_898 ::
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_events'8734''45''8776'_898 = erased
-- Once.Denotation.TraceMonadInfLaws.events∞-≈F
d_events'8734''45''8776'F_912 ::
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_NodeEq_158 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_events'8734''45''8776'F_912 = erased
-- Once.Denotation.TraceMonadInfLaws.events∞-≈C
d_events'8734''45''8776'C_934 ::
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Trace.T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_TreeEq'8734'_202) ->
  Maybe AgdaAny ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_events'8734''45''8776'C_934 = erased
-- Once.Denotation.TraceMonadInfLaws.RelT∞′-embed
d_RelT'8734''8242''45'embed_1012 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  T_RelT'8734''8242'_504
d_RelT'8734''8242''45'embed_1012 ~v0 ~v1 ~v2 v3 v4 v5
  = du_RelT'8734''8242''45'embed_1012 v3 v4 v5
du_RelT'8734''8242''45'embed_1012 ::
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542 ->
  T_RelT'8734''8242'_504
du_RelT'8734''8242''45'embed_1012 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Trace.C_rel'45'ret_554 v5
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Trace.C_ret_114 v6
               -> coe C_rel'8734''45'ret_518 v6 v5
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Trace.C_rel'45'call_566 v7
        -> case coe v0 of
             MAlonzo.Code.Once.Lang.Trace.C_call_118 v8 v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Lang.Trace.C_call_118 v11 v12 v13
                      -> coe
                           C_rel'8734''45'call_532
                           (\ v14 ->
                              coe MAlonzo.Code.Once.Lang.Iterative.du_embed_132 (coe v10 v14))
                           (\ v14 ->
                              coe
                                du_RelT'8734''8242''45'embed_1012 (coe v10 v14) (coe v13 v14)
                                (coe v7 v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Trace.C_rel'45'halt_572
        -> coe C_rel'8734''45'halt_540
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws.events∞-bnd
d_events'8734''45'bnd_1030 ::
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_events'8734''45'bnd_1030 ~v0 v1 v2 v3 v4
  = du_events'8734''45'bnd_1030 v1 v2 v3 v4
du_events'8734''45'bnd_1030 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_events'8734''45'bnd_1030 v0 v1 v2 v3
  = case coe v3 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v4 = subInt (coe v3) (coe (1 :: Integer)) in
           coe
             (coe
                du_eventsF'45'bnd_1042 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Lang.Iterative.d_force_84 (coe v2))
                (coe v4))
-- Once.Denotation.TraceMonadInfLaws.eventsF-bnd
d_eventsF'45'bnd_1042 ::
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_eventsF'45'bnd_1042 ~v0 v1 v2 v3 v4
  = du_eventsF'45'bnd_1042 v1 v2 v3 v4
du_eventsF'45'bnd_1042 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_eventsF'45'bnd_1042 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Iterative.C_ret'8734'_66 v4
        -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      MAlonzo.Code.Once.Lang.Iterative.C_call'8734'_70 v4 v5 v6
        -> coe
             du_eventsC'45'bnd_1060 (coe v0) (coe v1) (coe v4) (coe v5) (coe v6)
             (coe
                MAlonzo.Code.Once.Lang.Trace.d_callAnswer_330 (coe v0) (coe v1)
                (coe v4) (coe v5))
             (coe v3)
      MAlonzo.Code.Once.Lang.Iterative.C_halt'8734'_74 v4 v5
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws.eventsC-bnd
d_eventsC'45'bnd_1060 ::
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Trace.T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  Maybe AgdaAny ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_eventsC'45'bnd_1060 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_eventsC'45'bnd_1060 v1 v2 v3 v4 v5 v6 v7
du_eventsC'45'bnd_1060 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Trace.T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  Maybe AgdaAny ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_eventsC'45'bnd_1060 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (coe
                du_events'8734''45'bnd_1030 (coe v0)
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
                   (coe
                      MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                      (coe
                         MAlonzo.Code.Once.Lang.Trace.d_callEvent_94 (coe v2) (coe v3))))
                (coe v4 v7) (coe v6))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws.events∞-coh
d_events'8734''45'coh_1144 ::
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_events'8734''45'coh_1144 ~v0 v1 v2 v3 v4
  = du_events'8734''45'coh_1144 v1 v2 v3 v4
du_events'8734''45'coh_1144 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_events'8734''45'coh_1144 v0 v1 v2 v3
  = case coe v3 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Once.Lang.Iterative.du_eventsF_224 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Lang.Iterative.d_force_84 (coe v2))
                (coe (0 :: Integer)))
             erased
      _ -> let v4 = subInt (coe v3) (coe (1 :: Integer)) in
           coe
             (coe
                du_eventsF'45'coh_1158 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Lang.Iterative.d_force_84 (coe v2))
                (coe v4))
-- Once.Denotation.TraceMonadInfLaws.eventsF-coh
d_eventsF'45'coh_1158 ::
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_eventsF'45'coh_1158 ~v0 v1 v2 v3 v4
  = du_eventsF'45'coh_1158 v1 v2 v3 v4
du_eventsF'45'coh_1158 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_eventsF'45'coh_1158 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Iterative.C_ret'8734'_66 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) erased
      MAlonzo.Code.Once.Lang.Iterative.C_call'8734'_70 v4 v5 v6
        -> coe
             du_eventsC'45'coh_1178 (coe v0) (coe v1) (coe v4) (coe v5) (coe v6)
             (coe
                MAlonzo.Code.Once.Lang.Trace.d_callAnswer_330 (coe v0) (coe v1)
                (coe v4) (coe v5))
             (coe v3)
      MAlonzo.Code.Once.Lang.Iterative.C_halt'8734'_74 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws.eventsC-coh
d_eventsC'45'coh_1178 ::
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Trace.T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  Maybe AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_eventsC'45'coh_1178 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_eventsC'45'coh_1178 v1 v2 v3 v4 v5 v6 v7
du_eventsC'45'coh_1178 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Trace.T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  Maybe AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_eventsC'45'coh_1178 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                (coe
                   du_ih_1242 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v7)
                   (coe v6)))
             erased
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.TraceMonadInfLaws._.ih
d_ih_1242 ::
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Trace.T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ih_1242 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_ih_1242 v1 v2 v3 v4 v5 v6 v7
du_ih_1242 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Trace.T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ih_1242 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_events'8734''45'coh_1144 (coe v0)
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
         (coe
            MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
            (coe
               MAlonzo.Code.Once.Lang.Trace.d_callEvent_94 (coe v2) (coe v3))))
      (coe v4 v5) (coe v6)
-- Once.Denotation.TraceMonadInfLaws.events∞-sat
d_events'8734''45'sat_1268 ::
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_events'8734''45'sat_1268 = erased
-- Once.Denotation.TraceMonadInfLaws.eventsF-sat
d_eventsF'45'sat_1280 ::
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eventsF'45'sat_1280 = erased
-- Once.Denotation.TraceMonadInfLaws.eventsC-sat
d_eventsC'45'sat_1298 ::
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Trace.T_CallOp_56 ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  Maybe AgdaAny ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eventsC'45'sat_1298 = erased
-- Once.Denotation.TraceMonadInfLaws.events∞-pf
d_events'8734''45'pf_1392 ::
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Trace.T_PrefixFamily_476
d_events'8734''45'pf_1392 ~v0 v1 v2 v3
  = du_events'8734''45'pf_1392 v1 v2 v3
du_events'8734''45'pf_1392 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Trace.T_PrefixFamily_476
du_events'8734''45'pf_1392 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Trace.C_prefixFamily_492
      (coe du_events'8734''45'bnd_1030 (coe v0) (coe v1) (coe v2))
      (coe du_events'8734''45'coh_1144 (coe v0) (coe v1) (coe v2))
