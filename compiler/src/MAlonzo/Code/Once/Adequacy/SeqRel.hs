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

module MAlonzo.Code.Once.Adequacy.SeqRel where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Denotation.TraceMonadLaws
import qualified MAlonzo.Code.Once.Lang.Stream
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Lang.Type

-- Once.Adequacy.SeqRel.RelF
d_RelF_14 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () -> () -> (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> AgdaAny -> ()
d_RelF_14 = erased
-- Once.Adequacy.SeqRel.seqF-rel
d_seqF'45'rel_88 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
d_seqF'45'rel_88 v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_seqF'45'rel_88 v0 v4 v5 v6
du_seqF'45'rel_88 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_RelT'8242'_542
du_seqF'45'rel_88 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_K_12 v4
        -> coe MAlonzo.Code.Once.Lang.Trace.C_rel'45'ret_554 v3
      MAlonzo.Code.Once.Lang.Type.C_Id_14 -> coe v3
      MAlonzo.Code.Once.Lang.Type.C__'8853'__16 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'fmap_350
                           (coe MAlonzo.Code.Once.Lang.Stream.du_seqF_34 (coe v4) (coe v6))
                           (coe MAlonzo.Code.Once.Lang.Stream.du_seqF_34 (coe v4) (coe v7))
                           (coe (\ v8 v9 v10 -> v10))
                           (coe du_seqF'45'rel_88 (coe v4) (coe v6) (coe v7) (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'fmap_350
                           (coe MAlonzo.Code.Once.Lang.Stream.du_seqF_34 (coe v5) (coe v6))
                           (coe MAlonzo.Code.Once.Lang.Stream.du_seqF_34 (coe v5) (coe v7))
                           (coe (\ v8 v9 v10 -> v10))
                           (coe du_seqF'45'rel_88 (coe v5) (coe v6) (coe v7) (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C__'8855'__18 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                             -> coe
                                  MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'bind_300
                                  (coe MAlonzo.Code.Once.Lang.Stream.du_seqF_34 (coe v4) (coe v6))
                                  (coe MAlonzo.Code.Once.Lang.Stream.du_seqF_34 (coe v4) (coe v8))
                                  (coe du_seqF'45'rel_88 (coe v4) (coe v6) (coe v8) (coe v10))
                                  (coe
                                     (\ v12 v13 v14 ->
                                        coe
                                          MAlonzo.Code.Once.Denotation.TraceMonadLaws.du_RelT'8242''45'bind_300
                                          (coe
                                             MAlonzo.Code.Once.Lang.Stream.du_seqF_34 (coe v5)
                                             (coe v7))
                                          (coe
                                             MAlonzo.Code.Once.Lang.Stream.du_seqF_34 (coe v5)
                                             (coe v9))
                                          (coe
                                             du_seqF'45'rel_88 (coe v5) (coe v7) (coe v9) (coe v11))
                                          (coe
                                             (\ v15 v16 v17 ->
                                                coe
                                                  MAlonzo.Code.Once.Lang.Trace.C_rel'45'ret_554
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v14) (coe v17))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
