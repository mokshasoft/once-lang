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

module MAlonzo.Code.Once.Arith.Backend.CallAnswer where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Once.Lang.Contract
import qualified MAlonzo.Code.Once.Lang.Event
import qualified MAlonzo.Code.Once.Lang.Name
import qualified MAlonzo.Code.Once.Lang.Polynomial
import qualified MAlonzo.Code.Once.Lang.Res
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Value
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Arith.Backend.CallAnswer.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_10 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_10
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'base'45'to'45'full_404
-- Once.Arith.Backend.CallAnswer.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_12 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_12
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'full'45'to'45'base_372
-- Once.Arith.Backend.CallAnswer.M.coerce-functor
d_coerce'45'functor_14 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor_14 v0 v1 v2
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'functor_246 v0 v2
-- Once.Arith.Backend.CallAnswer.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_16 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_16 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'functor'8315''185'_288 v0
      v2
-- Once.Arith.Backend.CallAnswer.M.coerce-μ-in
d_coerce'45'μ'45'in_18 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_18 v0 v1 v2
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'in_436 v0 v2
-- Once.Arith.Backend.CallAnswer.M.coerce-μ-out
d_coerce'45'μ'45'out_20 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_20 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_478 v0 v1 v3
-- Once.Arith.Backend.CallAnswer.M.coerce-ν-in
d_coerce'45'ν'45'in_22 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_22
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578
-- Once.Arith.Backend.CallAnswer.M.coerce-ν-out
d_coerce'45'ν'45'out_24 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_24
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'out_584
-- Once.Arith.Backend.CallAnswer.M.eraseᵍ
d_erase'7501'_26 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_erase'7501'_26
  = coe MAlonzo.Code.Once.Lang.Value.du_erase'7501'_104
-- Once.Arith.Backend.CallAnswer.M.sem-CoIn
d_sem'45'CoIn_28 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
d_sem'45'CoIn_28
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'CoIn_598
-- Once.Arith.Backend.CallAnswer.M.sem-CoOut
d_sem'45'CoOut_30 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_νS_98 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
d_sem'45'CoOut_30
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'CoOut_588
-- Once.Arith.Backend.CallAnswer.M.sem-In
d_sem'45'In_32 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_μS_82
d_sem'45'In_32 = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'In_518
-- Once.Arith.Backend.CallAnswer.M.sem-Out
d_sem'45'Out_34 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'Out_34
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'Out_526
-- Once.Arith.Backend.CallAnswer.M.sem-ana
d_sem'45'ana_36 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
d_sem'45'ana_36 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'ana_608 v0 v2 v3
-- Once.Arith.Backend.CallAnswer.M.sem-cata
d_sem'45'cata_38 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'cata_38 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'cata_538 v0 v1 v3
-- Once.Arith.Backend.CallAnswer.M.sem-fmap
d_sem'45'fmap_40 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_40 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'fmap_332 v0 v3 v4
-- Once.Arith.Backend.CallAnswer.M.sem-para
d_sem'45'para_42 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'para_42 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'para_554 v0 v1 v3 v4
-- Once.Arith.Backend.CallAnswer.M.semAnaLayer
d_semAnaLayer_44 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
d_semAnaLayer_44 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_semAnaLayer_614 v0 v2 v3
-- Once.Arith.Backend.CallAnswer.M.sfmapSemAna
d_sfmapSemAna_46 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> AgdaAny
d_sfmapSemAna_46 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sfmapSemAna_622 v0 v1 v3 v4
-- Once.Arith.Backend.CallAnswer.M.⟦_⟧
d_'10214'_'10215'_48 :: MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_'10214'_'10215'_48 = erased
-- Once.Arith.Backend.CallAnswer.M.⟦_⟧F
d_'10214'_'10215'F_50 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> ()
d_'10214'_'10215'F_50 = erased
-- Once.Arith.Backend.CallAnswer.M.⟦_⟧ᵍ
d_'10214'_'10215''7501'_52 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_'10214'_'10215''7501'_52 = erased
-- Once.Arith.Backend.CallAnswer.M.⟦μ⟧
d_'10214'μ'10215'_54 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> ()
d_'10214'μ'10215'_54 = erased
-- Once.Arith.Backend.CallAnswer.M.⟦ν⟧
d_'10214'ν'10215'_56 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> ()
d_'10214'ν'10215'_56 = erased
-- Once.Arith.Backend.CallAnswer.answer-word
d_answer'45'word_60 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> Integer
d_answer'45'word_60 v0 v1
  = let v2 = 0 :: Integer in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.Lang.Type.C_Int_34 -> coe v1
         MAlonzo.Code.Once.Lang.Type.C_Float_36 -> coe v1
         _ -> coe v2)
-- Once.Arith.Backend.CallAnswer.ResolvedCall
d_ResolvedCall_66 = ()
data T_ResolvedCall_66
  = C_answering_70 MAlonzo.Code.Once.Lang.Trace.T_CallOp_56 AgdaAny |
    C_pure'45'ffi_78 MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6
                     MAlonzo.Code.Once.Lang.Type.T_Type_8
                     MAlonzo.Code.Once.Lang.Type.T_Type_8 AgdaAny |
    C_halting_80
-- Once.Arith.Backend.CallAnswer.CallResolver
d_CallResolver_82 :: () -> ()
d_CallResolver_82 = erased
-- Once.Arith.Backend.CallAnswer.answering-word
d_answering'45'word_90 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Once.Lang.Trace.T_CallOp_56 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
d_answering'45'word_90 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
        -> if coe v5
             then case coe v6 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v7
                      -> coe
                           d_answer'45'word_60
                           (coe MAlonzo.Code.Once.Lang.Trace.d_ccod_72 (coe v2))
                           (coe MAlonzo.Code.Once.Lang.Trace.d_answer_206 v0 v1 v2 v7 v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe seq (coe v6) (coe (0 :: Integer))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.CallAnswer.value-word
d_value'45'word_114 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  MAlonzo.Code.Once.Lang.Contract.T_Key_56 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 -> Integer
d_value'45'word_114 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
        -> if coe v4
             then case coe v5 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                      -> coe
                           d_answer'45'word_60
                           (coe MAlonzo.Code.Once.Lang.Contract.d_kcod_68 (coe v1))
                           (coe MAlonzo.Code.Once.Lang.Trace.d_pure_220 v0 v1 v6 v2)
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe seq (coe v5) (coe (0 :: Integer))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.CallAnswer.resolved-word
d_resolved'45'word_130 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  T_ResolvedCall_66 -> Maybe Integer
d_resolved'45'word_130 v0 v1 v2
  = case coe v2 of
      C_answering_70 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                d_answering'45'word_90 (coe v0) (coe v1) (coe v3) (coe v4)
                (coe
                   MAlonzo.Code.Once.Lang.Contract.d__'8712'K'63'__108
                   (MAlonzo.Code.Once.Lang.Trace.d_callKey_178 (coe v3))
                   (MAlonzo.Code.Once.Lang.Trace.d_calls_194 (coe v0))))
      C_pure'45'ffi_78 v3 v4 v5 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                d_value'45'word_114 (coe v0)
                (coe
                   MAlonzo.Code.Once.Lang.Contract.C_key_70
                   (coe MAlonzo.Code.Once.Lang.Name.d_showCanonical_6 (coe v3))
                   (coe v4) (coe v5))
                (coe v6)
                (coe
                   MAlonzo.Code.Once.Lang.Contract.d__'8712'K'63'__108
                   (coe
                      MAlonzo.Code.Once.Lang.Contract.C_key_70
                      (coe MAlonzo.Code.Once.Lang.Name.d_showCanonical_6 (coe v3))
                      (coe v4) (coe v5))
                   (MAlonzo.Code.Once.Lang.Trace.d_pures_196 (coe v0))))
      C_halting_80 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Arith.Backend.CallAnswer.answer-at
d_answer'45'at_158 ::
  () ->
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> Maybe T_ResolvedCall_66) ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny -> Maybe Integer
d_answer'45'at_158 ~v0 v1 v2 v3 v4 v5
  = du_answer'45'at_158 v1 v2 v3 v4 v5
du_answer'45'at_158 ::
  MAlonzo.Code.Once.Lang.Trace.T_Interp_182 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   AgdaAny -> Maybe T_ResolvedCall_66) ->
  [MAlonzo.Code.Once.Lang.Event.T_SigOpEvent_56] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny -> Maybe Integer
du_answer'45'at_158 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_maybe'8242'_44
      (d_resolved'45'word_130 (coe v0) (coe v2))
      (coe
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer)))
      (coe v1 v3 v4)
