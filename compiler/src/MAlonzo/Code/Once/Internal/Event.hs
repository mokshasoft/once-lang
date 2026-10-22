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

module MAlonzo.Code.Once.Internal.Event where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Internal.Polynomial
import qualified MAlonzo.Code.Once.Internal.Res
import qualified MAlonzo.Code.Once.Internal.Value
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Signature
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Internal.Event.M.coerce-base-to-full
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
-- Once.Internal.Event.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_10 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_10 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'full'45'to'45'base_384
      v1 v2
-- Once.Internal.Event.M.coerce-functor
d_coerce'45'functor_12 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor_12 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'functor_252 v1 v3
-- Once.Internal.Event.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_14 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_14 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'functor'8315''185'_296
      v1 v3
-- Once.Internal.Event.M.coerce-μ-in
d_coerce'45'μ'45'in_16 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_16 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'in_454 v1 v3
-- Once.Internal.Event.M.coerce-μ-out
d_coerce'45'μ'45'out_18 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_18 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_500 v2 v3 v5
-- Once.Internal.Event.M.coerce-ν-in
d_coerce'45'ν'45'in_20 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_20 v0
  = coe MAlonzo.Code.Once.Internal.Value.du_coerce'45'ν'45'in_616
-- Once.Internal.Event.M.coerce-ν-out
d_coerce'45'ν'45'out_22 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_22 v0 v1 v2
  = coe MAlonzo.Code.Once.Internal.Value.du_coerce'45'ν'45'out_626 v2
-- Once.Internal.Event.M.eraseᵍ
d_erase'7501'_24 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_erase'7501'_24 v0 v1 v2
  = coe MAlonzo.Code.Once.Internal.Value.du_erase'7501'_110 v1 v2
-- Once.Internal.Event.M.sem-CoIn
d_sem'45'CoIn_26 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Polynomial.T_νS_98
d_sem'45'CoIn_26 v0 v1 v2
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'CoIn_646 v1 v2
-- Once.Internal.Event.M.sem-CoOut
d_sem'45'CoOut_28 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_νS_98 ->
  MAlonzo.Code.Once.Internal.Res.T_Res_8
d_sem'45'CoOut_28 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'CoOut_634 v2 v3 v4
-- Once.Internal.Event.M.sem-In
d_sem'45'In_30 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Polynomial.T_μS_82
d_sem'45'In_30 v0 v1 v2
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'In_542 v1 v2
-- Once.Internal.Event.M.sem-Out
d_sem'45'Out_32 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'Out_32 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'Out_554 v2 v3 v4
-- Once.Internal.Event.M.sem-ana
d_sem'45'ana_34 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Res.T_Res_8) ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Polynomial.T_νS_98
d_sem'45'ana_34 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Internal.Value.du_sem'45'ana_658 v0 v1 v3 v4
-- Once.Internal.Event.M.sem-cata
d_sem'45'cata_36 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'cata_36 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'cata_570 v2 v3 v5
-- Once.Internal.Event.M.sem-fmap
d_sem'45'fmap_38 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_38 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'fmap_342 v1 v4 v5
-- Once.Internal.Event.M.sem-para
d_sem'45'para_40 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'para_40 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Internal.Value.du_sem'45'para_590 v2 v3 v5 v6
-- Once.Internal.Event.M.semAnaLayer
d_semAnaLayer_42 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Res.T_Res_8) ->
  MAlonzo.Code.Once.Internal.Res.T_Res_8 ->
  MAlonzo.Code.Once.Internal.Res.T_Res_8
d_semAnaLayer_42 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Internal.Value.du_semAnaLayer_666 v0 v1 v3 v4
-- Once.Internal.Event.M.sfmapSemAna
d_sfmapSemAna_44 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Res.T_Res_8) ->
  AgdaAny -> AgdaAny
d_sfmapSemAna_44 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Internal.Value.du_sfmapSemAna_676 v0 v1 v2 v4 v5
-- Once.Internal.Event.M.⟦_⟧
d_'10214'_'10215'_46 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_'10214'_'10215'_46 = erased
-- Once.Internal.Event.M.⟦_⟧F
d_'10214'_'10215'F_48 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> ()
d_'10214'_'10215'F_48 = erased
-- Once.Internal.Event.M.⟦_⟧ᵍ
d_'10214'_'10215''7501'_50 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_'10214'_'10215''7501'_50 = erased
-- Once.Internal.Event.M.⟦μ⟧
d_'10214'μ'10215'_52 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> ()
d_'10214'μ'10215'_52 = erased
-- Once.Internal.Event.M.⟦ν⟧
d_'10214'ν'10215'_54 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> ()
d_'10214'ν'10215'_54 = erased
-- Once.Internal.Event.SigOpEvent
d_SigOpEvent_56 = ()
data T_SigOpEvent_56
  = C_mk'45'event_74 MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
                     MAlonzo.Code.Once.Spec.Type.T_Ty_8 AgdaAny
-- Once.Internal.Event.SigOpEvent.ev-name
d_ev'45'name_66 ::
  T_SigOpEvent_56 -> MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
d_ev'45'name_66 v0
  = case coe v0 of
      C_mk'45'event_74 v1 v2 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Event.SigOpEvent.ev-dom
d_ev'45'dom_68 ::
  T_SigOpEvent_56 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_ev'45'dom_68 v0
  = case coe v0 of
      C_mk'45'event_74 v1 v2 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Event.SigOpEvent.ev-arg
d_ev'45'arg_72 :: T_SigOpEvent_56 -> AgdaAny
d_ev'45'arg_72 v0
  = case coe v0 of
      C_mk'45'event_74 v1 v2 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Event.baseˡ
d_base'737'_80 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84
d_base'737'_80 ~v0 ~v1 v2 = du_base'737'_80 v2
du_base'737'_80 ::
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84
du_base'737'_80 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_b'45''42'_106 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Event.baseʳ
d_base'691'_88 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84
d_base'691'_88 ~v0 ~v1 v2 = du_base'691'_88 v2
du_base'691'_88 ::
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84
du_base'691'_88 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_b'45''42'_106 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Event.sumˡ
d_sum'737'_96 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84
d_sum'737'_96 ~v0 ~v1 v2 = du_sum'737'_96 v2
du_sum'737'_96 ::
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84
du_sum'737'_96 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_b'45''43'_112 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Event.sumʳ
d_sum'691'_104 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84
d_sum'691'_104 ~v0 ~v1 v2 = du_sum'691'_104 v2
du_sum'691'_104 ::
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84
du_sum'691'_104 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_b'45''43'_112 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Event.baseOf
d_baseOf_110 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Signature.T_BTy_6
d_baseOf_110 v0 ~v1 = du_baseOf_110 v0
du_baseOf_110 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Signature.T_BTy_6
du_baseOf_110 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe MAlonzo.Code.Once.Spec.Signature.C_unit_8
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe MAlonzo.Code.Once.Spec.Signature.C_void_10
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Signature.C__'42'__16
             (coe du_baseOf_110 (coe v1)) (coe du_baseOf_110 (coe v2))
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Signature.C__'43'__18
             (coe du_baseOf_110 (coe v1)) (coe du_baseOf_110 (coe v2))
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe MAlonzo.Code.Once.Spec.Signature.C_int_12
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe MAlonzo.Code.Once.Spec.Signature.C_float_14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Event.valOf
d_valOf_128 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> AgdaAny -> AgdaAny
d_valOf_128 v0 ~v1 = du_valOf_128 v0
du_valOf_128 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
du_valOf_128 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v1
        -> coe (\ v2 -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Spec.Type.C_Unit_18 -> coe (\ v1 -> v1)
      MAlonzo.Code.Once.Spec.Type.C_Void_20 -> coe (\ v1 -> v1)
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v1 v2
        -> coe
             (\ v3 ->
                case coe v3 of
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                    -> coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe du_valOf_128 v1 v4) (coe du_valOf_128 v2 v5)
                  _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v1 v2
        -> coe
             (\ v3 ->
                case coe v3 of
                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
                    -> coe
                         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe du_valOf_128 v1 v4)
                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
                    -> coe
                         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe du_valOf_128 v2 v4)
                  _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Spec.Type.C_Int_32 -> coe (\ v1 -> v1)
      MAlonzo.Code.Once.Spec.Type.C_Float_34 -> coe (\ v1 -> v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Event.toEvent
d_toEvent_164 ::
  T_SigOpEvent_56 -> MAlonzo.Code.Once.Spec.Signature.T_Event_246
d_toEvent_164 v0
  = case coe v0 of
      C_mk'45'event_74 v1 v2 v4
        -> coe
             MAlonzo.Code.Once.Spec.Signature.C_event_260 (coe v1)
             (coe du_baseOf_110 (coe v2)) (coe du_valOf_128 v2 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
