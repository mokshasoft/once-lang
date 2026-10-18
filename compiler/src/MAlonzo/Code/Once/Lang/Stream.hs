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

module MAlonzo.Code.Once.Lang.Stream where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Lang.FunctorMeaning
import qualified MAlonzo.Code.Once.Lang.Polynomial
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Value

-- Once.Lang.Stream._.coerce-ν-in
d_coerce'45'ν'45'in_8 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_8
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578
-- Once.Lang.Stream._.⟦_⟧F
d_'10214'_'10215'F_10 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> ()
d_'10214'_'10215'F_10 = erased
-- Once.Lang.Stream.νᵈ
d_ν'7496'_14 a0 = ()
data T_ν'7496'_14
  = C_constructor_22 MAlonzo.Code.Once.Lang.Trace.T_T_110
-- Once.Lang.Stream.νᵈ.forceᵈ
d_force'7496'_20 ::
  T_ν'7496'_14 -> MAlonzo.Code.Once.Lang.Trace.T_T_110
d_force'7496'_20 v0
  = case coe v0 of
      C_constructor_22 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Stream.in-νᵈ
d_in'45'ν'7496'_26 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  AgdaAny -> T_ν'7496'_14
d_in'45'ν'7496'_26 ~v0 v1 = du_in'45'ν'7496'_26 v1
du_in'45'ν'7496'_26 :: AgdaAny -> T_ν'7496'_14
du_in'45'ν'7496'_26 v0
  = coe
      C_constructor_22
      (coe MAlonzo.Code.Once.Lang.Trace.C_ret_114 (coe v0))
-- Once.Lang.Stream.seqF
d_seqF_34 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () -> AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110
d_seqF_34 v0 ~v1 v2 = du_seqF_34 v0 v2
du_seqF_34 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110
du_seqF_34 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_K_12 v2
        -> coe MAlonzo.Code.Once.Lang.Trace.du_returnT_126 v1
      MAlonzo.Code.Once.Lang.Type.C_Id_14 -> coe v1
      MAlonzo.Code.Once.Lang.Type.C__'8853'__16 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
                    (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
                    (coe du_seqF_34 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
                    (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
                    (coe du_seqF_34 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Type.C__'8855'__18 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                    (coe du_seqF_34 (coe v2) (coe v4))
                    (coe
                       (\ v6 ->
                          coe
                            MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                            (coe du_seqF_34 (coe v3) (coe v5))
                            (coe
                               (\ v7 ->
                                  coe
                                    MAlonzo.Code.Once.Lang.Trace.du_returnT_126
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                       (coe v7))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Stream.anaᵈ
d_ana'7496'_70 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny -> T_ν'7496'_14
d_ana'7496'_70 v0 ~v1 v2 v3 = du_ana'7496'_70 v0 v2 v3
du_ana'7496'_70 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny -> T_ν'7496'_14
du_ana'7496'_70 v0 v1 v2
  = coe
      C_constructor_22 (coe du_anaTree_76 (coe v0) (coe v1) (coe v1 v2))
-- Once.Lang.Stream.anaTree
d_anaTree_76 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110
d_anaTree_76 v0 ~v1 v2 v3 = du_anaTree_76 v0 v2 v3
du_anaTree_76 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110
du_anaTree_76 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Trace.C_ret_114 v3
        -> coe
             MAlonzo.Code.Once.Lang.Trace.C_ret_114
             (coe du_mapAna'7496'_84 (coe v0) (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Lang.Trace.C_call_118 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Trace.C_call_118 (coe v3) (coe v4)
             (coe (\ v6 -> coe du_anaTree_76 (coe v0) (coe v1) (coe v5 v6)))
      MAlonzo.Code.Once.Lang.Trace.C_halt_122 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Stream.mapAnaᵈ
d_mapAna'7496'_84 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny -> AgdaAny
d_mapAna'7496'_84 v0 v1 ~v2 v3 v4 = du_mapAna'7496'_84 v0 v1 v3 v4
du_mapAna'7496'_84 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny -> AgdaAny
du_mapAna'7496'_84 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Polynomial.C_SK_8 -> coe v3
      MAlonzo.Code.Once.Lang.Polynomial.C_SId_10
        -> coe du_ana'7496'_70 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8853'__12 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_mapAna'7496'_84 (coe v0) (coe v4) (coe v2) (coe v6))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_mapAna'7496'_84 (coe v0) (coe v5) (coe v2) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8855'__14 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_mapAna'7496'_84 (coe v0) (coe v4) (coe v2) (coe v6))
                    (coe du_mapAna'7496'_84 (coe v0) (coe v5) (coe v2) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Stream.anaFᵈ
d_anaF'7496'_168 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny -> T_ν'7496'_14
d_anaF'7496'_168 v0 ~v1 v2 = du_anaF'7496'_168 v0 v2
du_anaF'7496'_168 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110) ->
  AgdaAny -> T_ν'7496'_14
du_anaF'7496'_168 v0 v1
  = coe
      du_ana'7496'_70
      (coe
         MAlonzo.Code.Once.Lang.FunctorMeaning.du_translateF_56 (coe v0))
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
              (coe
                 MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578 v0 erased)
              (coe v1 v2)))
