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
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.SeqRel.RelF
d_RelF_14 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () -> () -> (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> AgdaAny -> ()
d_RelF_14 = erased
-- Once.Adequacy.SeqRel.seqF-rel
d_seqF'45'rel_88 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_1076
d_seqF'45'rel_88 v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_seqF'45'rel_88 v0 v4 v5 v6
du_seqF'45'rel_88 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_RelT'8242'_1076
du_seqF'45'rel_88 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_K_112 v4
        -> coe MAlonzo.Code.Once.Denotation.TraceMonad.C_rel'45'ret_1088 v3
      MAlonzo.Code.Once.Type.C_Id_114 -> coe v3
      MAlonzo.Code.Once.Type.C__'8853'__116 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonad.du_RelT'8242''45'fmap_1182
                           (coe
                              MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28 (coe v4)
                              (coe v6))
                           (coe
                              MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28 (coe v4)
                              (coe v7))
                           (coe (\ v8 v9 v10 -> v10))
                           (coe du_seqF'45'rel_88 (coe v4) (coe v6) (coe v7) (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonad.du_RelT'8242''45'fmap_1182
                           (coe
                              MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28 (coe v5)
                              (coe v6))
                           (coe
                              MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28 (coe v5)
                              (coe v7))
                           (coe (\ v8 v9 v10 -> v10))
                           (coe du_seqF'45'rel_88 (coe v5) (coe v6) (coe v7) (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8855'__118 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                             -> coe
                                  MAlonzo.Code.Once.Denotation.TraceMonad.du_RelT'8242''45'bind_1132
                                  (coe
                                     MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28 (coe v4)
                                     (coe v6))
                                  (coe
                                     MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28 (coe v4)
                                     (coe v8))
                                  (coe du_seqF'45'rel_88 (coe v4) (coe v6) (coe v8) (coe v10))
                                  (coe
                                     (\ v12 v13 v14 ->
                                        coe
                                          MAlonzo.Code.Once.Denotation.TraceMonad.du_RelT'8242''45'bind_1132
                                          (coe
                                             MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28
                                             (coe v5) (coe v7))
                                          (coe
                                             MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28
                                             (coe v5) (coe v9))
                                          (coe
                                             du_seqF'45'rel_88 (coe v5) (coe v7) (coe v9) (coe v11))
                                          (coe
                                             (\ v15 v16 v17 ->
                                                coe
                                                  MAlonzo.Code.Once.Denotation.TraceMonad.C_rel'45'ret_1088
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v14) (coe v17))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
