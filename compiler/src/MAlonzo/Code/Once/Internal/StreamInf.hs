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

module MAlonzo.Code.Once.Internal.StreamInf where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Internal.FunctorMeaning
import qualified MAlonzo.Code.Once.Internal.Iterative
import qualified MAlonzo.Code.Once.Internal.Polynomial
import qualified MAlonzo.Code.Once.Internal.Trace
import qualified MAlonzo.Code.Once.Internal.Value
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Internal.StreamInf._.coerce-ν-in
d_coerce'45'ν'45'in_8 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_8 v0
  = coe MAlonzo.Code.Once.Internal.Value.du_coerce'45'ν'45'in_616
-- Once.Internal.StreamInf._.⟦_⟧F
d_'10214'_'10215'F_10 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> ()
d_'10214'_'10215'F_10 = erased
-- Once.Internal.StreamInf.νᴵ
d_ν'7477'_14 a0 = ()
data T_ν'7477'_14
  = C_constructor_22 MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58
-- Once.Internal.StreamInf.νᴵ.forceᴵ
d_force'7477'_20 ::
  T_ν'7477'_14 -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58
d_force'7477'_20 v0
  = case coe v0 of
      C_constructor_22 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.StreamInf.in-νᴵ
d_in'45'ν'7477'_26 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  AgdaAny -> T_ν'7477'_14
d_in'45'ν'7477'_26 ~v0 v1 = du_in'45'ν'7477'_26 v1
du_in'45'ν'7477'_26 :: AgdaAny -> T_ν'7477'_14
du_in'45'ν'7477'_26 v0
  = coe
      C_constructor_22
      (coe
         MAlonzo.Code.Once.Internal.Iterative.C_constructor_66
         (coe
            MAlonzo.Code.Once.Internal.Trace.C_ret_114
            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v0))))
-- Once.Internal.StreamInf.anaᴵ
d_ana'7477'_34 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  AgdaAny -> T_ν'7477'_14
d_ana'7477'_34 v0 ~v1 v2 v3 = du_ana'7477'_34 v0 v2 v3
du_ana'7477'_34 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  AgdaAny -> T_ν'7477'_14
du_ana'7477'_34 v0 v1 v2
  = coe
      C_constructor_22 (coe du_anaRun_40 (coe v0) (coe v1) (coe v1 v2))
-- Once.Internal.StreamInf.anaRun
d_anaRun_40 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58
d_anaRun_40 v0 ~v1 v2 v3 = du_anaRun_40 v0 v2 v3
du_anaRun_40 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58 ->
  MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58
du_anaRun_40 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Internal.Iterative.C_constructor_66
      (coe
         du_anaBlock_46 (coe v0) (coe v1)
         (coe MAlonzo.Code.Once.Internal.Iterative.d_force_64 (coe v2)))
-- Once.Internal.StreamInf.anaBlock
d_anaBlock_46 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110
d_anaBlock_46 v0 ~v1 v2 v3 = du_anaBlock_46 v0 v2 v3
du_anaBlock_46 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110
du_anaBlock_46 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Internal.Trace.C_ret_114 v3
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Once.Internal.Trace.C_ret_114
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                       (coe du_mapAna'7477'_54 (coe v0) (coe v0) (coe v1) (coe v4)))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Once.Internal.Trace.C_ret_114
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe du_anaRun_40 (coe v0) (coe v1) (coe v4)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Trace.C_call_118 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Internal.Trace.C_call_118 (coe v3) (coe v4)
             (coe (\ v6 -> coe du_anaBlock_46 (coe v0) (coe v1) (coe v5 v6)))
      MAlonzo.Code.Once.Internal.Trace.C_halt_122 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.StreamInf.mapAnaᴵ
d_mapAna'7477'_54 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  AgdaAny -> AgdaAny
d_mapAna'7477'_54 v0 v1 ~v2 v3 v4 = du_mapAna'7477'_54 v0 v1 v3 v4
du_mapAna'7477'_54 ::
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  AgdaAny -> AgdaAny
du_mapAna'7477'_54 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Internal.Polynomial.C_SK_8 -> coe v3
      MAlonzo.Code.Once.Internal.Polynomial.C_SId_10
        -> coe du_ana'7477'_34 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.Internal.Polynomial.C__S'8853'__12 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_mapAna'7477'_54 (coe v0) (coe v4) (coe v2) (coe v6))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_mapAna'7477'_54 (coe v0) (coe v5) (coe v2) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Polynomial.C__S'8855'__14 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_mapAna'7477'_54 (coe v0) (coe v4) (coe v2) (coe v6))
                    (coe du_mapAna'7477'_54 (coe v0) (coe v5) (coe v2) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.StreamInf.anaFᴵ
d_anaF'7477'_152 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  AgdaAny -> T_ν'7477'_14
d_anaF'7477'_152 ~v0 v1 ~v2 v3 = du_anaF'7477'_152 v1 v3
du_anaF'7477'_152 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58) ->
  AgdaAny -> T_ν'7477'_14
du_anaF'7477'_152 v0 v1
  = coe
      du_ana'7477'_34
      (coe
         MAlonzo.Code.Once.Internal.FunctorMeaning.du_translateF_60
         (coe v0))
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Once.Internal.Iterative.du_fmap'8734'_358
              (coe
                 MAlonzo.Code.Once.Internal.Value.du_coerce'45'ν'45'in_616 v0
                 erased)
              (coe v1 v2)))
