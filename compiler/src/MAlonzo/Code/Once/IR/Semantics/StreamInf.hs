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

module MAlonzo.Code.Once.IR.Semantics.StreamInf where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.IR.Semantics.FunctorMeaning
import qualified MAlonzo.Code.Once.IR.Semantics.Iterative
import qualified MAlonzo.Code.Once.IR.Semantics.Trace
import qualified MAlonzo.Code.Once.IR.Semantics.Value
import qualified MAlonzo.Code.Once.Spec.Polynomial
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.IR.Semantics.StreamInf._.coerce-ν-in
d_coerce'45'ν'45'in_10 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_10 v0
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'ν'45'in_618
-- Once.IR.Semantics.StreamInf._.⟦_⟧F
d_'10214'_'10215'F_12 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> ()
d_'10214'_'10215'F_12 = erased
-- Once.IR.Semantics.StreamInf.νᴵ
d_ν'7477'_16 a0 = ()
data T_ν'7477'_16
  = C_constructor_24 MAlonzo.Code.Once.IR.Semantics.Iterative.T_T'8734'_60
-- Once.IR.Semantics.StreamInf.νᴵ.forceᴵ
d_force'7477'_22 ::
  T_ν'7477'_16 ->
  MAlonzo.Code.Once.IR.Semantics.Iterative.T_T'8734'_60
d_force'7477'_22 v0
  = case coe v0 of
      C_constructor_24 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.StreamInf.in-νᴵ
d_in'45'ν'7477'_28 ::
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  AgdaAny -> T_ν'7477'_16
d_in'45'ν'7477'_28 ~v0 v1 = du_in'45'ν'7477'_28 v1
du_in'45'ν'7477'_28 :: AgdaAny -> T_ν'7477'_16
du_in'45'ν'7477'_28 v0
  = coe
      C_constructor_24
      (coe
         MAlonzo.Code.Once.IR.Semantics.Iterative.C_constructor_68
         (coe
            MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116
            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v0))))
-- Once.IR.Semantics.StreamInf.anaᴵ
d_ana'7477'_36 ::
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.Once.IR.Semantics.Iterative.T_T'8734'_60) ->
  AgdaAny -> T_ν'7477'_16
d_ana'7477'_36 v0 ~v1 v2 v3 = du_ana'7477'_36 v0 v2 v3
du_ana'7477'_36 ::
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  (AgdaAny ->
   MAlonzo.Code.Once.IR.Semantics.Iterative.T_T'8734'_60) ->
  AgdaAny -> T_ν'7477'_16
du_ana'7477'_36 v0 v1 v2
  = coe
      C_constructor_24 (coe du_anaRun_42 (coe v0) (coe v1) (coe v1 v2))
-- Once.IR.Semantics.StreamInf.anaRun
d_anaRun_42 ::
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.Once.IR.Semantics.Iterative.T_T'8734'_60) ->
  MAlonzo.Code.Once.IR.Semantics.Iterative.T_T'8734'_60 ->
  MAlonzo.Code.Once.IR.Semantics.Iterative.T_T'8734'_60
d_anaRun_42 v0 ~v1 v2 v3 = du_anaRun_42 v0 v2 v3
du_anaRun_42 ::
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  (AgdaAny ->
   MAlonzo.Code.Once.IR.Semantics.Iterative.T_T'8734'_60) ->
  MAlonzo.Code.Once.IR.Semantics.Iterative.T_T'8734'_60 ->
  MAlonzo.Code.Once.IR.Semantics.Iterative.T_T'8734'_60
du_anaRun_42 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.Semantics.Iterative.C_constructor_68
      (coe
         du_anaBlock_48 (coe v0) (coe v1)
         (coe MAlonzo.Code.Once.IR.Semantics.Iterative.d_force_66 (coe v2)))
-- Once.IR.Semantics.StreamInf.anaBlock
d_anaBlock_48 ::
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.Once.IR.Semantics.Iterative.T_T'8734'_60) ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
d_anaBlock_48 v0 ~v1 v2 v3 = du_anaBlock_48 v0 v2 v3
du_anaBlock_48 ::
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  (AgdaAny ->
   MAlonzo.Code.Once.IR.Semantics.Iterative.T_T'8734'_60) ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
du_anaBlock_48 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116 v3
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                       (coe du_mapAna'7477'_56 (coe v0) (coe v0) (coe v1) (coe v4)))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe du_anaRun_42 (coe v0) (coe v1) (coe v4)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.Semantics.Trace.C_call_120 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.IR.Semantics.Trace.C_call_120 (coe v3) (coe v4)
             (coe (\ v6 -> coe du_anaBlock_48 (coe v0) (coe v1) (coe v5 v6)))
      MAlonzo.Code.Once.IR.Semantics.Trace.C_halt_124 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.StreamInf.mapAnaᴵ
d_mapAna'7477'_56 ::
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.Once.IR.Semantics.Iterative.T_T'8734'_60) ->
  AgdaAny -> AgdaAny
d_mapAna'7477'_56 v0 v1 ~v2 v3 v4 = du_mapAna'7477'_56 v0 v1 v3 v4
du_mapAna'7477'_56 ::
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  (AgdaAny ->
   MAlonzo.Code.Once.IR.Semantics.Iterative.T_T'8734'_60) ->
  AgdaAny -> AgdaAny
du_mapAna'7477'_56 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Polynomial.C_SK_8 -> coe v3
      MAlonzo.Code.Once.Spec.Polynomial.C_SId_10
        -> coe du_ana'7477'_36 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.Spec.Polynomial.C__S'8853'__12 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_mapAna'7477'_56 (coe v0) (coe v4) (coe v2) (coe v6))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_mapAna'7477'_56 (coe v0) (coe v5) (coe v2) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Polynomial.C__S'8855'__14 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_mapAna'7477'_56 (coe v0) (coe v4) (coe v2) (coe v6))
                    (coe du_mapAna'7477'_56 (coe v0) (coe v5) (coe v2) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.StreamInf.anaFᴵ
d_anaF'7477'_154 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () ->
  (AgdaAny ->
   MAlonzo.Code.Once.IR.Semantics.Iterative.T_T'8734'_60) ->
  AgdaAny -> T_ν'7477'_16
d_anaF'7477'_154 ~v0 v1 ~v2 v3 = du_anaF'7477'_154 v1 v3
du_anaF'7477'_154 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  (AgdaAny ->
   MAlonzo.Code.Once.IR.Semantics.Iterative.T_T'8734'_60) ->
  AgdaAny -> T_ν'7477'_16
du_anaF'7477'_154 v0 v1
  = coe
      du_ana'7477'_36
      (coe
         MAlonzo.Code.Once.IR.Semantics.FunctorMeaning.du_translateF_62
         (coe v0))
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Once.IR.Semantics.Iterative.du_fmap'8734'_360
              (coe
                 MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'ν'45'in_618 v0
                 erased)
              (coe v1 v2)))
