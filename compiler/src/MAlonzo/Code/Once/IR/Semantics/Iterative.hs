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
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.IR.Semantics.Polynomial
import qualified MAlonzo.Code.Once.IR.Semantics.Trace
import qualified MAlonzo.Code.Once.IR.Semantics.Value
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.Spec.Polynomial
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.IR.Semantics.Iterative.V.coerce-base-to-full
d_coerce'45'base'45'to'45'full_10 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_10 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'base'45'to'45'full_422
      v2 v3 v4
-- Once.IR.Semantics.Iterative.V.coerce-full-to-base
d_coerce'45'full'45'to'45'base_12 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_12 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'full'45'to'45'base_386
      v1 v2
-- Once.IR.Semantics.Iterative.V.coerce-functor
d_coerce'45'functor_14 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor_14 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'functor_254 v1 v3
-- Once.IR.Semantics.Iterative.V.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_16 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_16 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'functor'8315''185'_298
      v1 v3
-- Once.IR.Semantics.Iterative.V.coerce-μ-in
d_coerce'45'μ'45'in_18 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_18 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'μ'45'in_456 v1 v3
-- Once.IR.Semantics.Iterative.V.coerce-μ-out
d_coerce'45'μ'45'out_20 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_20 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'μ'45'out_502 v2
      v3 v5
-- Once.IR.Semantics.Iterative.V.coerce-ν-in
d_coerce'45'ν'45'in_22 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_22 v0
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'ν'45'in_618
-- Once.IR.Semantics.Iterative.V.coerce-ν-out
d_coerce'45'ν'45'out_24 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_24 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'ν'45'out_628 v2
-- Once.IR.Semantics.Iterative.V.eraseᵍ
d_erase'7501'_26 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_erase'7501'_26 v0 v1 v2
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_erase'7501'_112 v1 v2
-- Once.IR.Semantics.Iterative.V.sem-CoIn
d_sem'45'CoIn_28 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Polynomial.T_νS_18
d_sem'45'CoIn_28 v0 v1 v2
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'CoIn_648 v1 v2
-- Once.IR.Semantics.Iterative.V.sem-CoOut
d_sem'45'CoOut_30 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.IR.Semantics.Polynomial.T_νS_18 ->
  MAlonzo.Code.Once.Res.T_Res_6
d_sem'45'CoOut_30 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'CoOut_636 v2 v3 v4
-- Once.IR.Semantics.Iterative.V.sem-In
d_sem'45'In_32 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Polynomial.T_μS_82
d_sem'45'In_32 v0 v1 v2
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'In_544 v1 v2
-- Once.IR.Semantics.Iterative.V.sem-Out
d_sem'45'Out_34 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'Out_34 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'Out_556 v2 v3 v4
-- Once.IR.Semantics.Iterative.V.sem-ana
d_sem'45'ana_36 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Polynomial.T_νS_18
d_sem'45'ana_36 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'ana_660 v0 v1 v3 v4
-- Once.IR.Semantics.Iterative.V.sem-cata
d_sem'45'cata_38 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'cata_38 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'cata_572 v2 v3 v5
-- Once.IR.Semantics.Iterative.V.sem-fmap
d_sem'45'fmap_40 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_40 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'fmap_344 v1 v4 v5
-- Once.IR.Semantics.Iterative.V.sem-para
d_sem'45'para_42 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'para_42 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'para_592 v2 v3 v5 v6
-- Once.IR.Semantics.Iterative.V.semAnaLayer
d_semAnaLayer_44 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Res.T_Res_6 -> MAlonzo.Code.Once.Res.T_Res_6
d_semAnaLayer_44 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_semAnaLayer_668 v0 v1 v3 v4
-- Once.IR.Semantics.Iterative.V.sfmapSemAna
d_sfmapSemAna_46 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) -> AgdaAny -> AgdaAny
d_sfmapSemAna_46 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sfmapSemAna_678 v0 v1 v2 v4
      v5
-- Once.IR.Semantics.Iterative.V.⟦_⟧
d_'10214'_'10215'_48 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_'10214'_'10215'_48 = erased
-- Once.IR.Semantics.Iterative.V.⟦_⟧F
d_'10214'_'10215'F_50 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> ()
d_'10214'_'10215'F_50 = erased
-- Once.IR.Semantics.Iterative.V.⟦_⟧ᵍ
d_'10214'_'10215''7501'_52 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_'10214'_'10215''7501'_52 = erased
-- Once.IR.Semantics.Iterative.V.⟦μ⟧
d_'10214'μ'10215'_54 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> ()
d_'10214'μ'10215'_54 = erased
-- Once.IR.Semantics.Iterative.V.⟦ν⟧
d_'10214'ν'10215'_56 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> ()
d_'10214'ν'10215'_56 = erased
-- Once.IR.Semantics.Iterative.T∞
d_T'8734'_60 a0 = ()
data T_T'8734'_60
  = C_constructor_68 MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
-- Once.IR.Semantics.Iterative.T∞.force
d_force_66 ::
  T_T'8734'_60 -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
d_force_66 v0
  = case coe v0 of
      C_constructor_68 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Iterative.return∞
d_return'8734'_72 :: () -> AgdaAny -> T_T'8734'_60
d_return'8734'_72 ~v0 v1 = du_return'8734'_72 v1
du_return'8734'_72 :: AgdaAny -> T_T'8734'_60
du_return'8734'_72 v0
  = coe
      C_constructor_68
      (coe
         MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116
         (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v0)))
-- Once.IR.Semantics.Iterative._>>=∞_
d__'62''62''61''8734'__80 ::
  () ->
  () -> T_T'8734'_60 -> (AgdaAny -> T_T'8734'_60) -> T_T'8734'_60
d__'62''62''61''8734'__80 ~v0 ~v1 v2 v3
  = du__'62''62''61''8734'__80 v2 v3
du__'62''62''61''8734'__80 ::
  T_T'8734'_60 -> (AgdaAny -> T_T'8734'_60) -> T_T'8734'_60
du__'62''62''61''8734'__80 v0 v1
  = coe
      C_constructor_68
      (coe du_bindBlock_86 (coe d_force_66 (coe v0)) (coe v1))
-- Once.IR.Semantics.Iterative.bindBlock
d_bindBlock_86 ::
  () ->
  () ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  (AgdaAny -> T_T'8734'_60) ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
d_bindBlock_86 ~v0 ~v1 v2 v3 = du_bindBlock_86 v2 v3
du_bindBlock_86 ::
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  (AgdaAny -> T_T'8734'_60) ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
du_bindBlock_86 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116 v2
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
               -> coe d_force_66 (coe v1 v3)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
               -> coe
                    MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe du__'62''62''61''8734'__80 (coe v3) (coe v1)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.Semantics.Trace.C_call_120 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.IR.Semantics.Trace.C_call_120 (coe v2) (coe v3)
             (coe (\ v5 -> coe du_bindBlock_86 (coe v4 v5) (coe v1)))
      MAlonzo.Code.Once.IR.Semantics.Trace.C_halt_124 v2 v3 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Iterative.embedBlock
d_embedBlock_120 ::
  () ->
  () ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
d_embedBlock_120 ~v0 ~v1 v2 = du_embedBlock_120 v2
du_embedBlock_120 ::
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
du_embedBlock_120 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116 v1
        -> coe
             MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116
             (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v1))
      MAlonzo.Code.Once.IR.Semantics.Trace.C_call_120 v1 v2 v3
        -> coe
             MAlonzo.Code.Once.IR.Semantics.Trace.C_call_120 (coe v1) (coe v2)
             (coe (\ v4 -> coe du_embedBlock_120 (coe v3 v4)))
      MAlonzo.Code.Once.IR.Semantics.Trace.C_halt_124 v1 v2 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Iterative.embed
d_embed_138 ::
  () -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 -> T_T'8734'_60
d_embed_138 ~v0 v1 = du_embed_138 v1
du_embed_138 ::
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 -> T_T'8734'_60
du_embed_138 v0
  = coe C_constructor_68 (coe du_embedBlock_120 (coe v0))
-- Once.IR.Semantics.Iterative.loop
d_loop_146 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112) ->
  AgdaAny -> T_T'8734'_60
d_loop_146 ~v0 ~v1 v2 v3 = du_loop_146 v2 v3
du_loop_146 ::
  (AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112) ->
  AgdaAny -> T_T'8734'_60
du_loop_146 v0 v1
  = coe C_constructor_68 (coe du_loopBlock_152 (coe v0) (coe v0 v1))
-- Once.IR.Semantics.Iterative.loopBlock
d_loopBlock_152 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112) ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
d_loopBlock_152 ~v0 ~v1 v2 v3 = du_loopBlock_152 v2 v3
du_loopBlock_152 ::
  (AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112) ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
du_loopBlock_152 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116 v2
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> coe v1
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
               -> coe
                    MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe du_loop_146 (coe v0) (coe v3)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.Semantics.Trace.C_call_120 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.IR.Semantics.Trace.C_call_120 (coe v2) (coe v3)
             (coe (\ v5 -> coe du_loopBlock_152 (coe v0) (coe v4 v5)))
      MAlonzo.Code.Once.IR.Semantics.Trace.C_halt_124 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Iterative.NowB
d_NowB_184 ::
  () -> MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 -> ()
d_NowB_184 = erased
-- Once.IR.Semantics.Iterative.nowB
d_nowB_190 ::
  () ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 -> AgdaAny -> AgdaAny
d_nowB_190 ~v0 v1 ~v2 = du_nowB_190 v1
du_nowB_190 ::
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 -> AgdaAny
du_nowB_190 v0
  = case coe v0 of
      MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116 v1
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> coe v2
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Iterative.Now
d_Now_196 :: () -> T_T'8734'_60 -> ()
d_Now_196 = erased
-- Once.IR.Semantics.Iterative.valueNow
d_valueNow_204 :: () -> T_T'8734'_60 -> AgdaAny -> AgdaAny
d_valueNow_204 ~v0 v1 ~v2 = du_valueNow_204 v1
du_valueNow_204 :: T_T'8734'_60 -> AgdaAny
du_valueNow_204 v0 = coe du_nowB_190 (coe d_force_66 (coe v0))
-- Once.IR.Semantics.Iterative.iterRun
d_iterRun_214 ::
  () ->
  () -> (AgdaAny -> T_T'8734'_60) -> T_T'8734'_60 -> T_T'8734'_60
d_iterRun_214 ~v0 ~v1 v2 v3 = du_iterRun_214 v2 v3
du_iterRun_214 ::
  (AgdaAny -> T_T'8734'_60) -> T_T'8734'_60 -> T_T'8734'_60
du_iterRun_214 v0 v1
  = coe
      C_constructor_68
      (coe du_iterBlock_220 (coe v0) (coe d_force_66 (coe v1)))
-- Once.IR.Semantics.Iterative.iterBlock
d_iterBlock_220 ::
  () ->
  () ->
  (AgdaAny -> T_T'8734'_60) ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
d_iterBlock_220 ~v0 ~v1 v2 v3 = du_iterBlock_220 v2 v3
du_iterBlock_220 ::
  (AgdaAny -> T_T'8734'_60) ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112 ->
  MAlonzo.Code.Once.IR.Semantics.Trace.T_T_112
du_iterBlock_220 v0 v1
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
                              (coe du_iterRun_214 (coe v0) (coe v0 v4)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
               -> coe
                    MAlonzo.Code.Once.IR.Semantics.Trace.C_ret_116
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe du_iterRun_214 (coe v0) (coe v3)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.Semantics.Trace.C_call_120 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.IR.Semantics.Trace.C_call_120 (coe v2) (coe v3)
             (coe (\ v5 -> coe du_iterBlock_220 (coe v0) (coe v4 v5)))
      MAlonzo.Code.Once.IR.Semantics.Trace.C_halt_124 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Iterative.iter∞
d_iter'8734'_258 ::
  () -> () -> (AgdaAny -> T_T'8734'_60) -> AgdaAny -> T_T'8734'_60
d_iter'8734'_258 ~v0 ~v1 v2 v3 = du_iter'8734'_258 v2 v3
du_iter'8734'_258 ::
  (AgdaAny -> T_T'8734'_60) -> AgdaAny -> T_T'8734'_60
du_iter'8734'_258 v0 v1 = coe du_iterRun_214 (coe v0) (coe v0 v1)
-- Once.IR.Semantics.Iterative.BlockEq
d_BlockEq_268 a0 a1 a2 a3 = ()
data T_BlockEq_268
  = C_ret'8776'_278 AgdaAny |
    C_call'8776'_290 (AgdaAny -> T_BlockEq_268) | C_halt'8776'_296
-- Once.IR.Semantics.Iterative.StepEq
d_StepEq_306 a0 a1 a2 a3 a4 a5 = ()
data T_StepEq_306
  = C_done'8776'_320 AgdaAny | C_next'8776'_326 AgdaAny
-- Once.IR.Semantics.Iterative.TreeEq∞
d_TreeEq'8734'_336 a0 a1 a2 a3 = ()
data T_TreeEq'8734'_336 = C_constructor_350 T_BlockEq_268
-- Once.IR.Semantics.Iterative.TreeEq∞.force≈
d_force'8776'_348 :: T_TreeEq'8734'_336 -> T_BlockEq_268
d_force'8776'_348 v0
  = case coe v0 of
      C_constructor_350 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Iterative._.⟦_⟧F
d_'10214'_'10215'F_354 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> ()
d_'10214'_'10215'F_354 = erased
-- Once.IR.Semantics.Iterative.fmap∞
d_fmap'8734'_360 ::
  () -> () -> (AgdaAny -> AgdaAny) -> T_T'8734'_60 -> T_T'8734'_60
d_fmap'8734'_360 ~v0 ~v1 v2 v3 = du_fmap'8734'_360 v2 v3
du_fmap'8734'_360 ::
  (AgdaAny -> AgdaAny) -> T_T'8734'_60 -> T_T'8734'_60
du_fmap'8734'_360 v0 v1
  = coe
      du__'62''62''61''8734'__80 (coe v1)
      (coe (\ v2 -> coe du_return'8734'_72 (coe v0 v2)))
-- Once.IR.Semantics.Iterative.seqF∞
d_seqF'8734'_374 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () -> AgdaAny -> T_T'8734'_60
d_seqF'8734'_374 ~v0 v1 ~v2 v3 = du_seqF'8734'_374 v1 v3
du_seqF'8734'_374 ::
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> AgdaAny -> T_T'8734'_60
du_seqF'8734'_374 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_K_38 v2
        -> coe du_return'8734'_72 (coe v1)
      MAlonzo.Code.Once.Spec.Type.C_Id_40 -> coe v1
      MAlonzo.Code.Once.Spec.Type.C__'8853'__42 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    du_fmap'8734'_360 (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
                    (coe du_seqF'8734'_374 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    du_fmap'8734'_360 (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
                    (coe du_seqF'8734'_374 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C__'8855'__44 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    du__'62''62''61''8734'__80
                    (coe du_seqF'8734'_374 (coe v2) (coe v4))
                    (coe
                       (\ v6 ->
                          coe
                            du__'62''62''61''8734'__80
                            (coe du_seqF'8734'_374 (coe v3) (coe v5))
                            (coe
                               (\ v7 ->
                                  coe
                                    du_return'8734'_72
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                       (coe v7))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
