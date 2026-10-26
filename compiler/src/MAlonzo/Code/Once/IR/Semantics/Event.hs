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

module MAlonzo.Code.Once.IR.Semantics.Event where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.IR.Semantics.Polynomial
import qualified MAlonzo.Code.Once.IR.Semantics.Value
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Polynomial
import qualified MAlonzo.Code.Once.Spec.Signature
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.IR.Semantics.Event.M.coerce-base-to-full
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
-- Once.IR.Semantics.Event.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_12 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_12 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'full'45'to'45'base_386
      v1 v2
-- Once.IR.Semantics.Event.M.coerce-functor
d_coerce'45'functor_14 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor_14 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'functor_254 v1 v3
-- Once.IR.Semantics.Event.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_16 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_16 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'functor'8315''185'_298
      v1 v3
-- Once.IR.Semantics.Event.M.coerce-μ-in
d_coerce'45'μ'45'in_18 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_18 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'μ'45'in_456 v1 v3
-- Once.IR.Semantics.Event.M.coerce-μ-out
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
-- Once.IR.Semantics.Event.M.coerce-ν-in
d_coerce'45'ν'45'in_22 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_22 v0
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'ν'45'in_618
-- Once.IR.Semantics.Event.M.coerce-ν-out
d_coerce'45'ν'45'out_24 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_24 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'ν'45'out_628 v2
-- Once.IR.Semantics.Event.M.eraseᵍ
d_erase'7501'_26 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_erase'7501'_26 v0 v1 v2
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_erase'7501'_112 v1 v2
-- Once.IR.Semantics.Event.M.sem-CoIn
d_sem'45'CoIn_28 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Polynomial.T_νS_18
d_sem'45'CoIn_28 v0 v1 v2
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'CoIn_648 v1 v2
-- Once.IR.Semantics.Event.M.sem-CoOut
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
-- Once.IR.Semantics.Event.M.sem-In
d_sem'45'In_32 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Polynomial.T_μS_82
d_sem'45'In_32 v0 v1 v2
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'In_544 v1 v2
-- Once.IR.Semantics.Event.M.sem-Out
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
-- Once.IR.Semantics.Event.M.sem-ana
d_sem'45'ana_36 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Polynomial.T_νS_18
d_sem'45'ana_36 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'ana_660 v0 v1 v3 v4
-- Once.IR.Semantics.Event.M.sem-cata
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
-- Once.IR.Semantics.Event.M.sem-fmap
d_sem'45'fmap_40 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_40 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'fmap_344 v1 v4 v5
-- Once.IR.Semantics.Event.M.sem-para
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
-- Once.IR.Semantics.Event.M.semAnaLayer
d_semAnaLayer_44 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Res.T_Res_6 -> MAlonzo.Code.Once.Res.T_Res_6
d_semAnaLayer_44 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_semAnaLayer_668 v0 v1 v3 v4
-- Once.IR.Semantics.Event.M.sfmapSemAna
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
-- Once.IR.Semantics.Event.M.⟦_⟧
d_'10214'_'10215'_48 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_'10214'_'10215'_48 = erased
-- Once.IR.Semantics.Event.M.⟦_⟧F
d_'10214'_'10215'F_50 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> ()
d_'10214'_'10215'F_50 = erased
-- Once.IR.Semantics.Event.M.⟦_⟧ᵍ
d_'10214'_'10215''7501'_52 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_'10214'_'10215''7501'_52 = erased
-- Once.IR.Semantics.Event.M.⟦μ⟧
d_'10214'μ'10215'_54 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> ()
d_'10214'μ'10215'_54 = erased
-- Once.IR.Semantics.Event.M.⟦ν⟧
d_'10214'ν'10215'_56 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> ()
d_'10214'ν'10215'_56 = erased
-- Once.IR.Semantics.Event.SigOpEvent
d_SigOpEvent_58 = ()
data T_SigOpEvent_58
  = C_mk'45'event_76 MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
                     MAlonzo.Code.Once.Spec.Type.T_Ty_8 AgdaAny
-- Once.IR.Semantics.Event.SigOpEvent.ev-name
d_ev'45'name_68 ::
  T_SigOpEvent_58 -> MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
d_ev'45'name_68 v0
  = case coe v0 of
      C_mk'45'event_76 v1 v2 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Event.SigOpEvent.ev-dom
d_ev'45'dom_70 ::
  T_SigOpEvent_58 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_ev'45'dom_70 v0
  = case coe v0 of
      C_mk'45'event_76 v1 v2 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Event.SigOpEvent.ev-arg
d_ev'45'arg_74 :: T_SigOpEvent_58 -> AgdaAny
d_ev'45'arg_74 v0
  = case coe v0 of
      C_mk'45'event_76 v1 v2 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Event.baseˡ
d_base'737'_82 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84
d_base'737'_82 ~v0 ~v1 v2 = du_base'737'_82 v2
du_base'737'_82 ::
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84
du_base'737'_82 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_b'45''42'_106 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Event.baseʳ
d_base'691'_90 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84
d_base'691'_90 ~v0 ~v1 v2 = du_base'691'_90 v2
du_base'691'_90 ::
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84
du_base'691'_90 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_b'45''42'_106 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Event.sumˡ
d_sum'737'_98 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84
d_sum'737'_98 ~v0 ~v1 v2 = du_sum'737'_98 v2
du_sum'737'_98 ::
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84
du_sum'737'_98 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_b'45''43'_112 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Event.sumʳ
d_sum'691'_106 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84
d_sum'691'_106 ~v0 ~v1 v2 = du_sum'691'_106 v2
du_sum'691'_106 ::
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84
du_sum'691'_106 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_b'45''43'_112 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Event.baseOf
d_baseOf_112 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.Spec.Signature.T_BTy_6
d_baseOf_112 v0 ~v1 = du_baseOf_112 v0
du_baseOf_112 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Signature.T_BTy_6
du_baseOf_112 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe MAlonzo.Code.Once.Spec.Signature.C_unit_8
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe MAlonzo.Code.Once.Spec.Signature.C_void_10
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Signature.C__'42'__16
             (coe du_baseOf_112 (coe v1)) (coe du_baseOf_112 (coe v2))
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Signature.C__'43'__18
             (coe du_baseOf_112 (coe v1)) (coe du_baseOf_112 (coe v2))
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe MAlonzo.Code.Once.Spec.Signature.C_int_12
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe MAlonzo.Code.Once.Spec.Signature.C_float_14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Event.valOf
d_valOf_130 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> AgdaAny -> AgdaAny
d_valOf_130 v0 ~v1 = du_valOf_130 v0
du_valOf_130 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
du_valOf_130 v0
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
                         (coe du_valOf_130 v1 v4) (coe du_valOf_130 v2 v5)
                  _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v1 v2
        -> coe
             (\ v3 ->
                case coe v3 of
                  MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
                    -> coe
                         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe du_valOf_130 v1 v4)
                  MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
                    -> coe
                         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe du_valOf_130 v2 v4)
                  _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Spec.Type.C_Int_32 -> coe (\ v1 -> v1)
      MAlonzo.Code.Once.Spec.Type.C_Float_34 -> coe (\ v1 -> v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IR.Semantics.Event.toEvent
d_toEvent_166 ::
  T_SigOpEvent_58 -> MAlonzo.Code.Once.Spec.Signature.T_Event_246
d_toEvent_166 v0
  = case coe v0 of
      C_mk'45'event_76 v1 v2 v4
        -> coe
             MAlonzo.Code.Once.Spec.Signature.C_event_260 (coe v1)
             (coe du_baseOf_112 (coe v2)) (coe du_valOf_130 v2 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
