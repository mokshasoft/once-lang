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

module MAlonzo.Code.Once.Internal.Iterative where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Internal.Polynomial
import qualified MAlonzo.Code.Once.Internal.Trace
import qualified MAlonzo.Code.Once.Internal.Value
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.Spec.Polynomial
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Internal.Iterative.V.coerce-base-to-full
d_coerce'45'base'45'to'45'full_8 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_8 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'base'45'to'45'full_420
      v2 v3 v4
-- Once.Internal.Iterative.V.coerce-full-to-base
d_coerce'45'full'45'to'45'base_10 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_10 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'full'45'to'45'base_384
      v1 v2
-- Once.Internal.Iterative.V.coerce-functor
d_coerce'45'functor_12 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor_12 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'functor_252 v1 v3
-- Once.Internal.Iterative.V.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_14 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_14 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'functor'8315''185'_296
      v1 v3
-- Once.Internal.Iterative.V.coerce-μ-in
d_coerce'45'μ'45'in_16 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_16 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'in_454 v1 v3
-- Once.Internal.Iterative.V.coerce-μ-out
d_coerce'45'μ'45'out_18 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_18 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_500 v2 v3 v5
-- Once.Internal.Iterative.V.coerce-ν-in
d_coerce'45'ν'45'in_20 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_20 v0
  = coe MAlonzo.Code.Once.Internal.Value.du_coerce'45'ν'45'in_616
-- Once.Internal.Iterative.V.coerce-ν-out
d_coerce'45'ν'45'out_22 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_22 v0 v1 v2
  = coe MAlonzo.Code.Once.Internal.Value.du_coerce'45'ν'45'out_626 v2
-- Once.Internal.Iterative.V.eraseᵍ
d_erase'7501'_24 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_erase'7501'_24 v0 v1 v2
  = coe MAlonzo.Code.Once.Internal.Value.du_erase'7501'_110 v1 v2
-- Once.Internal.Iterative.V.sem-CoIn
d_sem'45'CoIn_26 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Polynomial.T_νS_16
d_sem'45'CoIn_26 v0 v1 v2
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'CoIn_646 v1 v2
-- Once.Internal.Iterative.V.sem-CoOut
d_sem'45'CoOut_28 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_νS_16 ->
  MAlonzo.Code.Once.Res.T_Res_6
d_sem'45'CoOut_28 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'CoOut_634 v2 v3 v4
-- Once.Internal.Iterative.V.sem-In
d_sem'45'In_30 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Polynomial.T_μS_82
d_sem'45'In_30 v0 v1 v2
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'In_542 v1 v2
-- Once.Internal.Iterative.V.sem-Out
d_sem'45'Out_32 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'Out_32 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'Out_554 v2 v3 v4
-- Once.Internal.Iterative.V.sem-ana
d_sem'45'ana_34 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Polynomial.T_νS_16
d_sem'45'ana_34 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Internal.Value.du_sem'45'ana_658 v0 v1 v3 v4
-- Once.Internal.Iterative.V.sem-cata
d_sem'45'cata_36 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'cata_36 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'cata_570 v2 v3 v5
-- Once.Internal.Iterative.V.sem-fmap
d_sem'45'fmap_38 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_38 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'fmap_342 v1 v4 v5
-- Once.Internal.Iterative.V.sem-para
d_sem'45'para_40 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'para_40 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Internal.Value.du_sem'45'para_590 v2 v3 v5 v6
-- Once.Internal.Iterative.V.semAnaLayer
d_semAnaLayer_42 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Res.T_Res_6 -> MAlonzo.Code.Once.Res.T_Res_6
d_semAnaLayer_42 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Internal.Value.du_semAnaLayer_666 v0 v1 v3 v4
-- Once.Internal.Iterative.V.sfmapSemAna
d_sfmapSemAna_44 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) -> AgdaAny -> AgdaAny
d_sfmapSemAna_44 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Internal.Value.du_sfmapSemAna_676 v0 v1 v2 v4 v5
-- Once.Internal.Iterative.V.⟦_⟧
d_'10214'_'10215'_46 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_'10214'_'10215'_46 = erased
-- Once.Internal.Iterative.V.⟦_⟧F
d_'10214'_'10215'F_48 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> ()
d_'10214'_'10215'F_48 = erased
-- Once.Internal.Iterative.V.⟦_⟧ᵍ
d_'10214'_'10215''7501'_50 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_'10214'_'10215''7501'_50 = erased
-- Once.Internal.Iterative.V.⟦μ⟧
d_'10214'μ'10215'_52 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> ()
d_'10214'μ'10215'_52 = erased
-- Once.Internal.Iterative.V.⟦ν⟧
d_'10214'ν'10215'_54 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> ()
d_'10214'ν'10215'_54 = erased
-- Once.Internal.Iterative.T∞
d_T'8734'_58 a0 = ()
data T_T'8734'_58
  = C_constructor_66 MAlonzo.Code.Once.Internal.Trace.T_T_110
-- Once.Internal.Iterative.T∞.force
d_force_64 ::
  T_T'8734'_58 -> MAlonzo.Code.Once.Internal.Trace.T_T_110
d_force_64 v0
  = case coe v0 of
      C_constructor_66 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Iterative.return∞
d_return'8734'_70 :: () -> AgdaAny -> T_T'8734'_58
d_return'8734'_70 ~v0 v1 = du_return'8734'_70 v1
du_return'8734'_70 :: AgdaAny -> T_T'8734'_58
du_return'8734'_70 v0
  = coe
      C_constructor_66
      (coe
         MAlonzo.Code.Once.Internal.Trace.C_ret_114
         (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v0)))
-- Once.Internal.Iterative._>>=∞_
d__'62''62''61''8734'__78 ::
  () ->
  () -> T_T'8734'_58 -> (AgdaAny -> T_T'8734'_58) -> T_T'8734'_58
d__'62''62''61''8734'__78 ~v0 ~v1 v2 v3
  = du__'62''62''61''8734'__78 v2 v3
du__'62''62''61''8734'__78 ::
  T_T'8734'_58 -> (AgdaAny -> T_T'8734'_58) -> T_T'8734'_58
du__'62''62''61''8734'__78 v0 v1
  = coe
      C_constructor_66
      (coe du_bindBlock_84 (coe d_force_64 (coe v0)) (coe v1))
-- Once.Internal.Iterative.bindBlock
d_bindBlock_84 ::
  () ->
  () ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  (AgdaAny -> T_T'8734'_58) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110
d_bindBlock_84 ~v0 ~v1 v2 v3 = du_bindBlock_84 v2 v3
du_bindBlock_84 ::
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  (AgdaAny -> T_T'8734'_58) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110
du_bindBlock_84 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Trace.C_ret_114 v2
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
               -> coe d_force_64 (coe v1 v3)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
               -> coe
                    MAlonzo.Code.Once.Internal.Trace.C_ret_114
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe du__'62''62''61''8734'__78 (coe v3) (coe v1)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Trace.C_call_118 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Internal.Trace.C_call_118 (coe v2) (coe v3)
             (coe (\ v5 -> coe du_bindBlock_84 (coe v4 v5) (coe v1)))
      MAlonzo.Code.Once.Internal.Trace.C_halt_122 v2 v3 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Iterative.embedBlock
d_embedBlock_118 ::
  () ->
  () ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110
d_embedBlock_118 ~v0 ~v1 v2 = du_embedBlock_118 v2
du_embedBlock_118 ::
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110
du_embedBlock_118 v0
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Trace.C_ret_114 v1
        -> coe
             MAlonzo.Code.Once.Internal.Trace.C_ret_114
             (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v1))
      MAlonzo.Code.Once.Internal.Trace.C_call_118 v1 v2 v3
        -> coe
             MAlonzo.Code.Once.Internal.Trace.C_call_118 (coe v1) (coe v2)
             (coe (\ v4 -> coe du_embedBlock_118 (coe v3 v4)))
      MAlonzo.Code.Once.Internal.Trace.C_halt_122 v1 v2 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Iterative.embed
d_embed_136 ::
  () -> MAlonzo.Code.Once.Internal.Trace.T_T_110 -> T_T'8734'_58
d_embed_136 ~v0 v1 = du_embed_136 v1
du_embed_136 ::
  MAlonzo.Code.Once.Internal.Trace.T_T_110 -> T_T'8734'_58
du_embed_136 v0
  = coe C_constructor_66 (coe du_embedBlock_118 (coe v0))
-- Once.Internal.Iterative.loop
d_loop_144 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Trace.T_T_110) ->
  AgdaAny -> T_T'8734'_58
d_loop_144 ~v0 ~v1 v2 v3 = du_loop_144 v2 v3
du_loop_144 ::
  (AgdaAny -> MAlonzo.Code.Once.Internal.Trace.T_T_110) ->
  AgdaAny -> T_T'8734'_58
du_loop_144 v0 v1
  = coe C_constructor_66 (coe du_loopBlock_150 (coe v0) (coe v0 v1))
-- Once.Internal.Iterative.loopBlock
d_loopBlock_150 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Trace.T_T_110) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110
d_loopBlock_150 ~v0 ~v1 v2 v3 = du_loopBlock_150 v2 v3
du_loopBlock_150 ::
  (AgdaAny -> MAlonzo.Code.Once.Internal.Trace.T_T_110) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110
du_loopBlock_150 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Internal.Trace.C_ret_114 v2
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> coe v1
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
               -> coe
                    MAlonzo.Code.Once.Internal.Trace.C_ret_114
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe du_loop_144 (coe v0) (coe v3)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Trace.C_call_118 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Internal.Trace.C_call_118 (coe v2) (coe v3)
             (coe (\ v5 -> coe du_loopBlock_150 (coe v0) (coe v4 v5)))
      MAlonzo.Code.Once.Internal.Trace.C_halt_122 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Iterative.NowB
d_NowB_182 :: () -> MAlonzo.Code.Once.Internal.Trace.T_T_110 -> ()
d_NowB_182 = erased
-- Once.Internal.Iterative.nowB
d_nowB_188 ::
  () ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 -> AgdaAny -> AgdaAny
d_nowB_188 ~v0 v1 ~v2 = du_nowB_188 v1
du_nowB_188 :: MAlonzo.Code.Once.Internal.Trace.T_T_110 -> AgdaAny
du_nowB_188 v0
  = case coe v0 of
      MAlonzo.Code.Once.Internal.Trace.C_ret_114 v1
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> coe v2
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Iterative.Now
d_Now_194 :: () -> T_T'8734'_58 -> ()
d_Now_194 = erased
-- Once.Internal.Iterative.valueNow
d_valueNow_202 :: () -> T_T'8734'_58 -> AgdaAny -> AgdaAny
d_valueNow_202 ~v0 v1 ~v2 = du_valueNow_202 v1
du_valueNow_202 :: T_T'8734'_58 -> AgdaAny
du_valueNow_202 v0 = coe du_nowB_188 (coe d_force_64 (coe v0))
-- Once.Internal.Iterative.iterRun
d_iterRun_212 ::
  () ->
  () -> (AgdaAny -> T_T'8734'_58) -> T_T'8734'_58 -> T_T'8734'_58
d_iterRun_212 ~v0 ~v1 v2 v3 = du_iterRun_212 v2 v3
du_iterRun_212 ::
  (AgdaAny -> T_T'8734'_58) -> T_T'8734'_58 -> T_T'8734'_58
du_iterRun_212 v0 v1
  = coe
      C_constructor_66
      (coe du_iterBlock_218 (coe v0) (coe d_force_64 (coe v1)))
-- Once.Internal.Iterative.iterBlock
d_iterBlock_218 ::
  () ->
  () ->
  (AgdaAny -> T_T'8734'_58) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110
d_iterBlock_218 ~v0 ~v1 v2 v3 = du_iterBlock_218 v2 v3
du_iterBlock_218 ::
  (AgdaAny -> T_T'8734'_58) ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110 ->
  MAlonzo.Code.Once.Internal.Trace.T_T_110
du_iterBlock_218 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Internal.Trace.C_ret_114 v2
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
               -> case coe v3 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
                      -> coe MAlonzo.Code.Once.Internal.Trace.C_ret_114 (coe v3)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
                      -> coe
                           MAlonzo.Code.Once.Internal.Trace.C_ret_114
                           (coe
                              MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                              (coe du_iterRun_212 (coe v0) (coe v0 v4)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
               -> coe
                    MAlonzo.Code.Once.Internal.Trace.C_ret_114
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe du_iterRun_212 (coe v0) (coe v3)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Internal.Trace.C_call_118 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Internal.Trace.C_call_118 (coe v2) (coe v3)
             (coe (\ v5 -> coe du_iterBlock_218 (coe v0) (coe v4 v5)))
      MAlonzo.Code.Once.Internal.Trace.C_halt_122 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Iterative.iter∞
d_iter'8734'_256 ::
  () -> () -> (AgdaAny -> T_T'8734'_58) -> AgdaAny -> T_T'8734'_58
d_iter'8734'_256 ~v0 ~v1 v2 v3 = du_iter'8734'_256 v2 v3
du_iter'8734'_256 ::
  (AgdaAny -> T_T'8734'_58) -> AgdaAny -> T_T'8734'_58
du_iter'8734'_256 v0 v1 = coe du_iterRun_212 (coe v0) (coe v0 v1)
-- Once.Internal.Iterative.BlockEq
d_BlockEq_266 a0 a1 a2 a3 = ()
data T_BlockEq_266
  = C_ret'8776'_276 AgdaAny |
    C_call'8776'_288 (AgdaAny -> T_BlockEq_266) | C_halt'8776'_294
-- Once.Internal.Iterative.StepEq
d_StepEq_304 a0 a1 a2 a3 a4 a5 = ()
data T_StepEq_304
  = C_done'8776'_318 AgdaAny | C_next'8776'_324 AgdaAny
-- Once.Internal.Iterative.TreeEq∞
d_TreeEq'8734'_334 a0 a1 a2 a3 = ()
data T_TreeEq'8734'_334 = C_constructor_348 T_BlockEq_266
-- Once.Internal.Iterative.TreeEq∞.force≈
d_force'8776'_346 :: T_TreeEq'8734'_334 -> T_BlockEq_266
d_force'8776'_346 v0
  = case coe v0 of
      C_constructor_348 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Iterative._.⟦_⟧F
d_'10214'_'10215'F_352 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> ()
d_'10214'_'10215'F_352 = erased
-- Once.Internal.Iterative.fmap∞
d_fmap'8734'_358 ::
  () -> () -> (AgdaAny -> AgdaAny) -> T_T'8734'_58 -> T_T'8734'_58
d_fmap'8734'_358 ~v0 ~v1 v2 v3 = du_fmap'8734'_358 v2 v3
du_fmap'8734'_358 ::
  (AgdaAny -> AgdaAny) -> T_T'8734'_58 -> T_T'8734'_58
du_fmap'8734'_358 v0 v1
  = coe
      du__'62''62''61''8734'__78 (coe v1)
      (coe (\ v2 -> coe du_return'8734'_70 (coe v0 v2)))
-- Once.Internal.Iterative.seqF∞
d_seqF'8734'_372 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () -> AgdaAny -> T_T'8734'_58
d_seqF'8734'_372 ~v0 v1 ~v2 v3 = du_seqF'8734'_372 v1 v3
du_seqF'8734'_372 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> AgdaAny -> T_T'8734'_58
du_seqF'8734'_372 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_K_38 v2
        -> coe du_return'8734'_70 (coe v1)
      MAlonzo.Code.Once.Spec.Type.C_Id_40 -> coe v1
      MAlonzo.Code.Once.Spec.Type.C__'8853'__42 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    du_fmap'8734'_358 (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
                    (coe du_seqF'8734'_372 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    du_fmap'8734'_358 (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
                    (coe du_seqF'8734'_372 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C__'8855'__44 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    du__'62''62''61''8734'__78
                    (coe du_seqF'8734'_372 (coe v2) (coe v4))
                    (coe
                       (\ v6 ->
                          coe
                            du__'62''62''61''8734'__78
                            (coe du_seqF'8734'_372 (coe v3) (coe v5))
                            (coe
                               (\ v7 ->
                                  coe
                                    du_return'8734'_70
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                       (coe v7))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
