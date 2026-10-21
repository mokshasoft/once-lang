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

module MAlonzo.Code.Once.Internal.Contract where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.List.Membership.DecSetoid
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Internal.Event
import qualified MAlonzo.Code.Once.Internal.Polynomial
import qualified MAlonzo.Code.Once.Internal.Res
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Internal.Type.DecEq
import qualified MAlonzo.Code.Once.Internal.Type.WellFormed
import qualified MAlonzo.Code.Once.Internal.Value
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Internal.Contract.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_8 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_8
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'base'45'to'45'full_404
-- Once.Internal.Contract.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_10 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_10
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'full'45'to'45'base_372
-- Once.Internal.Contract.M.coerce-functor
d_coerce'45'functor_12 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor_12 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'functor_246 v0 v2
-- Once.Internal.Contract.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_14 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_14 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'functor'8315''185'_288
      v0 v2
-- Once.Internal.Contract.M.coerce-μ-in
d_coerce'45'μ'45'in_16 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_16 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'in_436 v0 v2
-- Once.Internal.Contract.M.coerce-μ-out
d_coerce'45'μ'45'out_18 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_18 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_478 v0 v1 v3
-- Once.Internal.Contract.M.coerce-ν-in
d_coerce'45'ν'45'in_20 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_20
  = coe MAlonzo.Code.Once.Internal.Value.du_coerce'45'ν'45'in_578
-- Once.Internal.Contract.M.coerce-ν-out
d_coerce'45'ν'45'out_22 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_22
  = coe MAlonzo.Code.Once.Internal.Value.du_coerce'45'ν'45'out_584
-- Once.Internal.Contract.M.eraseᵍ
d_erase'7501'_24 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_erase'7501'_24
  = coe MAlonzo.Code.Once.Internal.Value.du_erase'7501'_104
-- Once.Internal.Contract.M.sem-CoIn
d_sem'45'CoIn_26 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Polynomial.T_νS_98
d_sem'45'CoIn_26
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'CoIn_598
-- Once.Internal.Contract.M.sem-CoOut
d_sem'45'CoOut_28 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_νS_98 ->
  MAlonzo.Code.Once.Internal.Res.T_Res_8
d_sem'45'CoOut_28
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'CoOut_588
-- Once.Internal.Contract.M.sem-In
d_sem'45'In_30 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Polynomial.T_μS_82
d_sem'45'In_30
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'In_518
-- Once.Internal.Contract.M.sem-Out
d_sem'45'Out_32 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'Out_32
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'Out_526
-- Once.Internal.Contract.M.sem-ana
d_sem'45'ana_34 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Res.T_Res_8) ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Polynomial.T_νS_98
d_sem'45'ana_34 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'ana_608 v0 v2 v3
-- Once.Internal.Contract.M.sem-cata
d_sem'45'cata_36 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'cata_36 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'cata_538 v0 v1 v3
-- Once.Internal.Contract.M.sem-fmap
d_sem'45'fmap_38 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_38 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'fmap_332 v0 v3 v4
-- Once.Internal.Contract.M.sem-para
d_sem'45'para_40 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'para_40 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Internal.Value.du_sem'45'para_554 v0 v1 v3 v4
-- Once.Internal.Contract.M.semAnaLayer
d_semAnaLayer_42 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Res.T_Res_8) ->
  MAlonzo.Code.Once.Internal.Res.T_Res_8 ->
  MAlonzo.Code.Once.Internal.Res.T_Res_8
d_semAnaLayer_42 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Internal.Value.du_semAnaLayer_614 v0 v2 v3
-- Once.Internal.Contract.M.sfmapSemAna
d_sfmapSemAna_44 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Internal.Res.T_Res_8) ->
  AgdaAny -> AgdaAny
d_sfmapSemAna_44 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Internal.Value.du_sfmapSemAna_622 v0 v1 v3 v4
-- Once.Internal.Contract.M.⟦_⟧
d_'10214'_'10215'_46 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> ()
d_'10214'_'10215'_46 = erased
-- Once.Internal.Contract.M.⟦_⟧F
d_'10214'_'10215'F_48 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 -> () -> ()
d_'10214'_'10215'F_48 = erased
-- Once.Internal.Contract.M.⟦_⟧ᵍ
d_'10214'_'10215''7501'_50 ::
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> ()
d_'10214'_'10215''7501'_50 = erased
-- Once.Internal.Contract.M.⟦μ⟧
d_'10214'μ'10215'_52 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 -> ()
d_'10214'μ'10215'_52 = erased
-- Once.Internal.Contract.M.⟦ν⟧
d_'10214'ν'10215'_54 ::
  MAlonzo.Code.Once.Internal.Type.T_Functor_6 -> ()
d_'10214'ν'10215'_54 = erased
-- Once.Internal.Contract.Key
d_Key_56 = ()
data T_Key_56
  = C_key_70 MAlonzo.Code.Agda.Builtin.String.T_String_6
             MAlonzo.Code.Once.Internal.Type.T_Type_8
             MAlonzo.Code.Once.Internal.Type.T_Type_8
-- Once.Internal.Contract.Key.kname
d_kname_64 ::
  T_Key_56 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_kname_64 v0
  = case coe v0 of
      C_key_70 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Contract.Key.kdom
d_kdom_66 :: T_Key_56 -> MAlonzo.Code.Once.Internal.Type.T_Type_8
d_kdom_66 v0
  = case coe v0 of
      C_key_70 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Contract.Key.kcod
d_kcod_68 :: T_Key_56 -> MAlonzo.Code.Once.Internal.Type.T_Type_8
d_kcod_68 v0
  = case coe v0 of
      C_key_70 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Contract._≟K_
d__'8799'K__72 ::
  T_Key_56 ->
  T_Key_56 -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'K__72 v0 v1
  = case coe v0 of
      C_key_70 v2 v3 v4
        -> case coe v1 of
             C_key_70 v5 v6 v7
               -> coe
                    du_go_90
                    (coe
                       MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v2)
                       (coe v5))
                    (coe
                       MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__216 (coe v3)
                       (coe v6))
                    (coe
                       MAlonzo.Code.Once.Internal.Type.DecEq.d__'8799'T__216 (coe v4)
                       (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Contract._.go
d_go_90 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_go_90 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 = du_go_90 v6 v7 v8
du_go_90 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_go_90 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                         -> if coe v5
                              then case coe v6 of
                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v7
                                       -> let v8
                                                = case coe v2 of
                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                                      -> case coe v8 of
                                                           MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                             -> case coe v9 of
                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                    -> coe
                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                         (coe v8)
                                                                         (coe
                                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                  _ -> coe
                                                                         seq (coe v8)
                                                                         (coe
                                                                            seq (coe v9)
                                                                            (coe
                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                               (coe v8)
                                                                               (coe
                                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                                                           _ -> coe
                                                                  seq (coe v8)
                                                                  (coe
                                                                     seq (coe v9)
                                                                     (coe
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                                                        (coe
                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                                                    _ -> MAlonzo.RTE.mazUnreachableError in
                                          coe
                                            (case coe v2 of
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                                 -> if coe v9
                                                      then case coe v10 of
                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v11
                                                               -> coe
                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                    (coe v9)
                                                                    (coe
                                                                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                       erased)
                                                             _ -> coe v8
                                                      else (case coe v10 of
                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                -> coe
                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                     (coe v9)
                                                                     (coe
                                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                              _ -> coe v8)
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     _ -> coe
                                            seq (coe v6)
                                            (case coe v2 of
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                                                 -> coe
                                                      seq (coe v7)
                                                      (coe
                                                         seq (coe v8)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                                            (coe
                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                              else (case coe v6 of
                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                        -> coe
                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                             (coe v5)
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                      _ -> coe
                                             seq (coe v6)
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                (coe v5)
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v4)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v3)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Contract._∈K?_
d__'8712'K'63'__108 ::
  T_Key_56 ->
  [T_Key_56] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8712'K'63'__108
  = coe
      MAlonzo.Code.Data.List.Membership.DecSetoid.du__'8712''63'__60
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
         (coe d__'8799'K__72))
-- Once.Internal.Contract.ISig
d_ISig_110 :: ()
d_ISig_110 = erased
-- Once.Internal.Contract.Contract
d_Contract_112 = ()
data T_Contract_112
  = C_value_114 T_Key_56 | C_answers_116 T_Key_56 | C_effect_118
-- Once.Internal.Contract.contract-eff
d_contract'45'eff_124 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Contract_112
d_contract'45'eff_124 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
        -> if coe v5
             then coe seq (coe v6) (coe C_effect_118)
             else coe
                    seq (coe v6)
                    (case coe v4 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                         -> if coe v7
                              then coe seq (coe v8) (coe C_effect_118)
                              else coe
                                     seq (coe v8)
                                     (coe C_answers_116 (coe C_key_70 (coe v0) (coe v1) (coe v2)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Contract.contractOf
d_contractOf_144 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Internal.Type.T_Type_8 -> T_Contract_112
d_contractOf_144 v0 v1
  = let v2
          = coe
              C_value_114
              (coe
                 C_key_70 (coe v0) (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                 (coe v1)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Internal.Type.C__'8658''91'_'93'__28 v3 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v6 v7
                  -> case coe v6 of
                       MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                         -> case coe v7 of
                              MAlonzo.Code.Once.Spec.Grade.C_fin_42 v8
                                -> case coe v8 of
                                     MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                                       -> coe
                                            C_value_114
                                            (coe
                                               C_key_70 (coe v0)
                                               (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20)
                                               (coe v5))
                                     MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                       -> coe
                                            d_contract'45'eff_124 (coe v0)
                                            (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20) (coe v5)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Type.d_isVoid'63'_84
                                               (coe v5))
                                            (coe
                                               MAlonzo.Code.Once.Internal.Type.d_isUnit'63'_88
                                               (coe v5))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                -> coe
                                     d_contract'45'eff_124 (coe v0)
                                     (coe MAlonzo.Code.Once.Internal.Type.C_Unit_20) (coe v5)
                                     (coe MAlonzo.Code.Once.Internal.Type.d_isVoid'63'_84 (coe v5))
                                     (coe MAlonzo.Code.Once.Internal.Type.d_isUnit'63'_88 (coe v5))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Once.Spec.Grade.C_One_10
                         -> case coe v7 of
                              MAlonzo.Code.Once.Spec.Grade.C_fin_42 v8
                                -> case coe v8 of
                                     MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                                       -> coe C_value_114 (coe C_key_70 (coe v0) (coe v3) (coe v5))
                                     MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                       -> coe
                                            d_contract'45'eff_124 (coe v0) (coe v3) (coe v5)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Type.d_isVoid'63'_84
                                               (coe v5))
                                            (coe
                                               MAlonzo.Code.Once.Internal.Type.d_isUnit'63'_88
                                               (coe v5))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                -> coe
                                     d_contract'45'eff_124 (coe v0) (coe v3) (coe v5)
                                     (coe MAlonzo.Code.Once.Internal.Type.d_isVoid'63'_84 (coe v5))
                                     (coe MAlonzo.Code.Once.Internal.Type.d_isUnit'63'_88 (coe v5))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Once.Spec.Grade.C_Many_12
                         -> case coe v7 of
                              MAlonzo.Code.Once.Spec.Grade.C_fin_42 v8
                                -> case coe v8 of
                                     MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                                       -> coe C_value_114 (coe C_key_70 (coe v0) (coe v3) (coe v5))
                                     MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                       -> coe
                                            d_contract'45'eff_124 (coe v0) (coe v3) (coe v5)
                                            (coe
                                               MAlonzo.Code.Once.Internal.Type.d_isVoid'63'_84
                                               (coe v5))
                                            (coe
                                               MAlonzo.Code.Once.Internal.Type.d_isUnit'63'_88
                                               (coe v5))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                -> coe
                                     d_contract'45'eff_124 (coe v0) (coe v3) (coe v5)
                                     (coe MAlonzo.Code.Once.Internal.Type.d_isVoid'63'_84 (coe v5))
                                     (coe MAlonzo.Code.Once.Internal.Type.d_isUnit'63'_88 (coe v5))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v2)
-- Once.Internal.Contract.value-step
d_value'45'step_204 :: T_Contract_112 -> [T_Key_56] -> [T_Key_56]
d_value'45'step_204 v0 v1
  = case coe v0 of
      C_value_114 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2) (coe v1)
      C_answers_116 v2 -> coe v1
      C_effect_118 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Contract.answer-step
d_answer'45'step_206 :: T_Contract_112 -> [T_Key_56] -> [T_Key_56]
d_answer'45'step_206 v0 v1
  = case coe v0 of
      C_value_114 v2 -> coe v1
      C_answers_116 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2) (coe v1)
      C_effect_118 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Contract.valueKeys
d_valueKeys_224 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> [T_Key_56]
d_valueKeys_224 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    d_value'45'step_204 (coe d_contractOf_144 (coe v3) (coe v4))
                    (coe d_valueKeys_224 (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Contract.answerKeys
d_answerKeys_226 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> [T_Key_56]
d_answerKeys_226 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    d_answer'45'step_206 (coe d_contractOf_144 (coe v3) (coe v4))
                    (coe d_answerKeys_226 (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Contract.Impl
d_Impl_242 a0 = ()
data T_Impl_242
  = C_constructor_262 ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
                       T_Key_56 ->
                       MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
                       AgdaAny -> AgdaAny)
                      (T_Key_56 ->
                       MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
                       AgdaAny -> AgdaAny)
-- Once.Internal.Contract.Impl.answerI
d_answerI_256 ::
  T_Impl_242 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  T_Key_56 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny -> AgdaAny
d_answerI_256 v0
  = case coe v0 of
      C_constructor_262 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Contract.Impl.pureI
d_pureI_260 ::
  T_Impl_242 ->
  T_Key_56 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny -> AgdaAny
d_pureI_260 v0
  = case coe v0 of
      C_constructor_262 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Contract.valueOf-at
d_valueOf'45'at_268 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_Impl_242 ->
  T_Key_56 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny
d_valueOf'45'at_268 ~v0 v1 v2 ~v3 v4
  = du_valueOf'45'at_268 v1 v2 v4
du_valueOf'45'at_268 ::
  T_Impl_242 ->
  T_Key_56 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny
du_valueOf'45'at_268 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then case coe v4 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v5
                      -> coe d_pureI_260 v0 v1 v5
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v4) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Internal.Contract.valueOf
d_valueOf_290 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_Impl_242 ->
  T_Key_56 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny -> AgdaAny
d_valueOf_290 v0 v1 v2 ~v3 = du_valueOf_290 v0 v1 v2
du_valueOf_290 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_Impl_242 -> T_Key_56 -> AgdaAny -> AgdaAny
du_valueOf_290 v0 v1 v2
  = coe
      du_valueOf'45'at_268 (coe v1) (coe v2)
      (coe d__'8712'K'63'__108 v2 (d_valueKeys_224 (coe v0)))
