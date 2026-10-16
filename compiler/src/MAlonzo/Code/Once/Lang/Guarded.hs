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

module MAlonzo.Code.Once.Lang.Guarded where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Lang.Iterative
import qualified MAlonzo.Code.Once.Lang.Polynomial
import qualified MAlonzo.Code.Once.Lang.Res
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Value

-- Once.Lang.Guarded.V.coerce-base-to-full
d_coerce'45'base'45'to'45'full_8 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_8
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'base'45'to'45'full_440
-- Once.Lang.Guarded.V.coerce-full-to-base
d_coerce'45'full'45'to'45'base_10 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_10
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'full'45'to'45'base_408
-- Once.Lang.Guarded.V.coerce-functor
d_coerce'45'functor_12 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor_12 v0 v1 v2
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'functor_282 v0 v2
-- Once.Lang.Guarded.V.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_14 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_14 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'functor'8315''185'_324 v0
      v2
-- Once.Lang.Guarded.V.coerce-μ-in
d_coerce'45'μ'45'in_16 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_16 v0 v1 v2
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'in_472 v0 v2
-- Once.Lang.Guarded.V.coerce-μ-out
d_coerce'45'μ'45'out_18 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_18 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_514 v0 v1 v3
-- Once.Lang.Guarded.V.coerce-ν-in
d_coerce'45'ν'45'in_20 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_20
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_614
-- Once.Lang.Guarded.V.coerce-ν-out
d_coerce'45'ν'45'out_22 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_22
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'out_620
-- Once.Lang.Guarded.V.eraseᵍ
d_erase'7501'_24 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_erase'7501'_24
  = coe MAlonzo.Code.Once.Lang.Value.du_erase'7501'_116
-- Once.Lang.Guarded.V.sem-CoIn
d_sem'45'CoIn_26 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
d_sem'45'CoIn_26
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'CoIn_634
-- Once.Lang.Guarded.V.sem-CoOut
d_sem'45'CoOut_28 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_νS_98 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
d_sem'45'CoOut_28
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'CoOut_624
-- Once.Lang.Guarded.V.sem-In
d_sem'45'In_30 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_μS_82
d_sem'45'In_30 = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'In_554
-- Once.Lang.Guarded.V.sem-Out
d_sem'45'Out_32 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'Out_32
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'Out_562
-- Once.Lang.Guarded.V.sem-ana
d_sem'45'ana_34 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
d_sem'45'ana_34 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'ana_644 v0 v2 v3
-- Once.Lang.Guarded.V.sem-cata
d_sem'45'cata_36 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'cata_36 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'cata_574 v0 v1 v3
-- Once.Lang.Guarded.V.sem-fmap
d_sem'45'fmap_38 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_38 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'fmap_368 v0 v3 v4
-- Once.Lang.Guarded.V.sem-para
d_sem'45'para_40 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'para_40 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'para_590 v0 v1 v3 v4
-- Once.Lang.Guarded.V.semAnaLayer
d_semAnaLayer_42 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
d_semAnaLayer_42 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_semAnaLayer_650 v0 v2 v3
-- Once.Lang.Guarded.V.sfmapSemAna
d_sfmapSemAna_44 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> AgdaAny
d_sfmapSemAna_44 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sfmapSemAna_658 v0 v1 v3 v4
-- Once.Lang.Guarded.V.⟦_⟧
d_'10214'_'10215'_46 :: MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_'10214'_'10215'_46 = erased
-- Once.Lang.Guarded.V.⟦_⟧F
d_'10214'_'10215'F_48 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> ()
d_'10214'_'10215'F_48 = erased
-- Once.Lang.Guarded.V.⟦_⟧ᵍ
d_'10214'_'10215''7501'_50 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_'10214'_'10215''7501'_50 = erased
-- Once.Lang.Guarded.V.⟦μ⟧
d_'10214'μ'10215'_52 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> ()
d_'10214'μ'10215'_52 = erased
-- Once.Lang.Guarded.V.⟦ν⟧
d_'10214'ν'10215'_54 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> ()
d_'10214'ν'10215'_54 = erased
-- Once.Lang.Guarded.T⁺
d_T'8314'_58 a0 = ()
data T_T'8314'_58
  = C_call'8314'_64 MAlonzo.Code.Once.Lang.Trace.T_CallOp_56 AgdaAny
                    (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) |
    C_halt'8314'_68 MAlonzo.Code.Once.Lang.Trace.T_HaltOp_76 AgdaAny
-- Once.Lang.Guarded.root⁺
d_root'8314'_72 ::
  () ->
  T_T'8314'_58 -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60
d_root'8314'_72 ~v0 v1 = du_root'8314'_72 v1
du_root'8314'_72 ::
  T_T'8314'_58 -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60
du_root'8314'_72 v0
  = case coe v0 of
      C_call'8314'_64 v1 v2 v3
        -> coe
             MAlonzo.Code.Once.Lang.Iterative.C_call'8734'_70 (coe v1) (coe v2)
             (coe v3)
      C_halt'8314'_68 v1 v2
        -> coe
             MAlonzo.Code.Once.Lang.Iterative.C_halt'8734'_74 (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Guarded.forget⁺
d_forget'8314'_86 ::
  () -> T_T'8314'_58 -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78
d_forget'8314'_86 ~v0 v1 = du_forget'8314'_86 v1
du_forget'8314'_86 ::
  T_T'8314'_58 -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78
du_forget'8314'_86 v0
  = coe
      MAlonzo.Code.Once.Lang.Iterative.C_constructor_86
      (coe du_root'8314'_72 (coe v0))
-- Once.Lang.Guarded._>>=⁺_
d__'62''62''61''8314'__94 ::
  () ->
  () ->
  T_T'8314'_58 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  T_T'8314'_58
d__'62''62''61''8314'__94 ~v0 ~v1 v2 v3
  = du__'62''62''61''8314'__94 v2 v3
du__'62''62''61''8314'__94 ::
  T_T'8314'_58 ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78) ->
  T_T'8314'_58
du__'62''62''61''8314'__94 v0 v1
  = case coe v0 of
      C_call'8314'_64 v2 v3 v4
        -> coe
             C_call'8314'_64 (coe v2) (coe v3)
             (coe
                (\ v5 ->
                   coe
                     MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__98
                     (coe v4 v5) (coe v1)))
      C_halt'8314'_68 v2 v3 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Guarded.bindF⁺
d_bindF'8314'_116 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  (AgdaAny -> T_T'8314'_58) -> T_T'8314'_58
d_bindF'8314'_116 ~v0 ~v1 v2 v3 = du_bindF'8314'_116 v2 v3
du_bindF'8314'_116 ::
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  (AgdaAny -> T_T'8314'_58) -> T_T'8314'_58
du_bindF'8314'_116 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Iterative.C_ret'8734'_66 v2 -> coe v1 v2
      MAlonzo.Code.Once.Lang.Iterative.C_call'8734'_70 v2 v3 v4
        -> coe
             C_call'8314'_64 (coe v2) (coe v3)
             (coe
                (\ v5 ->
                   coe
                     MAlonzo.Code.Once.Lang.Iterative.du__'62''62''61''8734'__98
                     (coe v4 v5) (coe (\ v6 -> coe du_forget'8314'_86 (coe v1 v6)))))
      MAlonzo.Code.Once.Lang.Iterative.C_halt'8734'_74 v2 v3
        -> coe C_halt'8314'_68 (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Guarded._⁺=<<_
d__'8314''61''60''60'__144 ::
  () ->
  () ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  (AgdaAny -> T_T'8314'_58) -> T_T'8314'_58
d__'8314''61''60''60'__144 ~v0 ~v1 v2 v3
  = du__'8314''61''60''60'__144 v2 v3
du__'8314''61''60''60'__144 ::
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  (AgdaAny -> T_T'8314'_58) -> T_T'8314'_58
du__'8314''61''60''60'__144 v0 v1
  = coe
      du_bindF'8314'_116
      (coe MAlonzo.Code.Once.Lang.Iterative.d_force_84 (coe v0)) (coe v1)
-- Once.Lang.Guarded.fmap⁺
d_fmap'8314'_154 ::
  () -> () -> (AgdaAny -> AgdaAny) -> T_T'8314'_58 -> T_T'8314'_58
d_fmap'8314'_154 ~v0 ~v1 v2 v3 = du_fmap'8314'_154 v2 v3
du_fmap'8314'_154 ::
  (AgdaAny -> AgdaAny) -> T_T'8314'_58 -> T_T'8314'_58
du_fmap'8314'_154 v0 v1
  = coe
      du__'62''62''61''8314'__94 (coe v1)
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Once.Lang.Iterative.du_return'8734'_90 (coe v0 v2)))
-- Once.Lang.Guarded.ν⁺
d_ν'8314'_164 a0 = ()
data T_ν'8314'_164 = C_constructor_172 T_T'8314'_58
-- Once.Lang.Guarded.ν⁺.force⁺
d_force'8314'_170 :: T_ν'8314'_164 -> T_T'8314'_58
d_force'8314'_170 v0
  = case coe v0 of
      C_constructor_172 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Guarded.ana⁺
d_ana'8314'_178 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () -> (AgdaAny -> T_T'8314'_58) -> AgdaAny -> T_ν'8314'_164
d_ana'8314'_178 v0 ~v1 v2 v3 = du_ana'8314'_178 v0 v2 v3
du_ana'8314'_178 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> T_T'8314'_58) -> AgdaAny -> T_ν'8314'_164
du_ana'8314'_178 v0 v1 v2
  = coe
      C_constructor_172
      (coe du_anaRoot'8314'_184 (coe v0) (coe v1) (coe v1 v2))
-- Once.Lang.Guarded.anaRoot⁺
d_anaRoot'8314'_184 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () -> (AgdaAny -> T_T'8314'_58) -> T_T'8314'_58 -> T_T'8314'_58
d_anaRoot'8314'_184 v0 ~v1 v2 v3 = du_anaRoot'8314'_184 v0 v2 v3
du_anaRoot'8314'_184 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> T_T'8314'_58) -> T_T'8314'_58 -> T_T'8314'_58
du_anaRoot'8314'_184 v0 v1 v2
  = case coe v2 of
      C_call'8314'_64 v3 v4 v5
        -> coe
             C_call'8314'_64 (coe v3) (coe v4)
             (coe
                (\ v6 -> coe du_anaTree'8314'_190 (coe v0) (coe v1) (coe v5 v6)))
      C_halt'8314'_68 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Guarded.anaTree⁺
d_anaTree'8314'_190 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> T_T'8314'_58) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78
d_anaTree'8314'_190 v0 ~v1 v2 v3 = du_anaTree'8314'_190 v0 v2 v3
du_anaTree'8314'_190 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> T_T'8314'_58) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78
du_anaTree'8314'_190 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Iterative.C_constructor_86
      (coe
         du_anaLayer'8314'_196 (coe v0) (coe v1)
         (coe MAlonzo.Code.Once.Lang.Iterative.d_force_84 (coe v2)))
-- Once.Lang.Guarded.anaLayer⁺
d_anaLayer'8314'_196 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> T_T'8314'_58) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60
d_anaLayer'8314'_196 v0 ~v1 v2 v3 = du_anaLayer'8314'_196 v0 v2 v3
du_anaLayer'8314'_196 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> T_T'8314'_58) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60
du_anaLayer'8314'_196 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Lang.Iterative.C_ret'8734'_66 v3
        -> coe
             MAlonzo.Code.Once.Lang.Iterative.C_ret'8734'_66
             (coe du_mapAna'8314'_204 (coe v0) (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Once.Lang.Iterative.C_call'8734'_70 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.Lang.Iterative.C_call'8734'_70 (coe v3) (coe v4)
             (coe
                (\ v6 -> coe du_anaTree'8314'_190 (coe v0) (coe v1) (coe v5 v6)))
      MAlonzo.Code.Once.Lang.Iterative.C_halt'8734'_74 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Guarded.mapAna⁺
d_mapAna'8314'_204 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () -> (AgdaAny -> T_T'8314'_58) -> AgdaAny -> AgdaAny
d_mapAna'8314'_204 v0 v1 ~v2 v3 v4
  = du_mapAna'8314'_204 v0 v1 v3 v4
du_mapAna'8314'_204 ::
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  (AgdaAny -> T_T'8314'_58) -> AgdaAny -> AgdaAny
du_mapAna'8314'_204 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Polynomial.C_SK_8 -> coe v3
      MAlonzo.Code.Once.Lang.Polynomial.C_SId_10
        -> coe du_ana'8314'_178 (coe v0) (coe v2) (coe v3)
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8853'__12 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe du_mapAna'8314'_204 (coe v0) (coe v4) (coe v2) (coe v6))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe du_mapAna'8314'_204 (coe v0) (coe v5) (coe v2) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Polynomial.C__S'8855'__14 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_mapAna'8314'_204 (coe v0) (coe v4) (coe v2) (coe v6))
                    (coe du_mapAna'8314'_204 (coe v0) (coe v5) (coe v2) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Guarded.iter∞
d_iter'8734'_314 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78
d_iter'8734'_314 ~v0 ~v1 v2 v3 = du_iter'8734'_314 v2 v3
du_iter'8734'_314 ::
  (AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78
du_iter'8734'_314 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Iterative.C_constructor_86
      (coe du_iterStart'8734'_320 (coe v0) (coe v0 v1))
-- Once.Lang.Guarded.iterStart∞
d_iterStart'8734'_320 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60
d_iterStart'8734'_320 ~v0 ~v1 v2 v3 = du_iterStart'8734'_320 v2 v3
du_iterStart'8734'_320 ::
  (AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60
du_iterStart'8734'_320 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
        -> coe MAlonzo.Code.Once.Lang.Iterative.C_ret'8734'_66 (coe v2)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> coe du_iterRoot'8734'_326 (coe v0) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Guarded.iterRoot∞
d_iterRoot'8734'_326 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  T_T'8314'_58 -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60
d_iterRoot'8734'_326 ~v0 ~v1 v2 v3 = du_iterRoot'8734'_326 v2 v3
du_iterRoot'8734'_326 ::
  (AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  T_T'8314'_58 -> MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60
du_iterRoot'8734'_326 v0 v1
  = case coe v1 of
      C_call'8314'_64 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Iterative.C_call'8734'_70 (coe v2) (coe v3)
             (coe (\ v5 -> coe du_iterTree'8734'_332 (coe v0) (coe v4 v5)))
      C_halt'8314'_68 v2 v3
        -> coe
             MAlonzo.Code.Once.Lang.Iterative.C_halt'8734'_74 (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Guarded.iterTree∞
d_iterTree'8734'_332 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78
d_iterTree'8734'_332 ~v0 ~v1 v2 v3 = du_iterTree'8734'_332 v2 v3
du_iterTree'8734'_332 ::
  (AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'_78
du_iterTree'8734'_332 v0 v1
  = coe
      MAlonzo.Code.Once.Lang.Iterative.C_constructor_86
      (coe
         du_iterLayer'8734'_338 (coe v0)
         (coe MAlonzo.Code.Once.Lang.Iterative.d_force_84 (coe v1)))
-- Once.Lang.Guarded.iterLayer∞
d_iterLayer'8734'_338 ::
  () ->
  () ->
  (AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60
d_iterLayer'8734'_338 ~v0 ~v1 v2 v3 = du_iterLayer'8734'_338 v2 v3
du_iterLayer'8734'_338 ::
  (AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60 ->
  MAlonzo.Code.Once.Lang.Iterative.T_T'8734'F_60
du_iterLayer'8734'_338 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Lang.Iterative.C_ret'8734'_66 v2
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
               -> coe MAlonzo.Code.Once.Lang.Iterative.C_ret'8734'_66 (coe v3)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
               -> coe du_iterStart'8734'_320 (coe v0) (coe v0 v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Iterative.C_call'8734'_70 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.Lang.Iterative.C_call'8734'_70 (coe v2) (coe v3)
             (coe (\ v5 -> coe du_iterTree'8734'_332 (coe v0) (coe v4 v5)))
      MAlonzo.Code.Once.Lang.Iterative.C_halt'8734'_74 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
