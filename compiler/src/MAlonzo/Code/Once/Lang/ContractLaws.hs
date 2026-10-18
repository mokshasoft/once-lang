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

module MAlonzo.Code.Once.Lang.ContractLaws where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Once.Lang.Contract
import qualified MAlonzo.Code.Once.Lang.Polynomial
import qualified MAlonzo.Code.Once.Lang.Res
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Value
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Lang.ContractLaws.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_8 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_8
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'base'45'to'45'full_404
-- Once.Lang.ContractLaws.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_10 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_10
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'full'45'to'45'base_372
-- Once.Lang.ContractLaws.M.coerce-functor
d_coerce'45'functor_12 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor_12 v0 v1 v2
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'functor_246 v0 v2
-- Once.Lang.ContractLaws.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_14 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_14 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'functor'8315''185'_288 v0
      v2
-- Once.Lang.ContractLaws.M.coerce-μ-in
d_coerce'45'μ'45'in_16 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_16 v0 v1 v2
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'in_436 v0 v2
-- Once.Lang.ContractLaws.M.coerce-μ-out
d_coerce'45'μ'45'out_18 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_18 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Value.du_coerce'45'μ'45'out_478 v0 v1 v3
-- Once.Lang.ContractLaws.M.coerce-ν-in
d_coerce'45'ν'45'in_20 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_20
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'in_578
-- Once.Lang.ContractLaws.M.coerce-ν-out
d_coerce'45'ν'45'out_22 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_22
  = coe MAlonzo.Code.Once.Lang.Value.du_coerce'45'ν'45'out_584
-- Once.Lang.ContractLaws.M.eraseᵍ
d_erase'7501'_24 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> AgdaAny -> AgdaAny
d_erase'7501'_24
  = coe MAlonzo.Code.Once.Lang.Value.du_erase'7501'_104
-- Once.Lang.ContractLaws.M.sem-CoIn
d_sem'45'CoIn_26 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
d_sem'45'CoIn_26
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'CoIn_598
-- Once.Lang.ContractLaws.M.sem-CoOut
d_sem'45'CoOut_28 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_νS_98 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
d_sem'45'CoOut_28
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'CoOut_588
-- Once.Lang.ContractLaws.M.sem-In
d_sem'45'In_30 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_μS_82
d_sem'45'In_30 = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'In_518
-- Once.Lang.ContractLaws.M.sem-Out
d_sem'45'Out_32 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'Out_32
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'Out_526
-- Once.Lang.ContractLaws.M.sem-ana
d_sem'45'ana_34 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Polynomial.T_νS_98
d_sem'45'ana_34 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'ana_608 v0 v2 v3
-- Once.Lang.ContractLaws.M.sem-cata
d_sem'45'cata_36 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'cata_36 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'cata_538 v0 v1 v3
-- Once.Lang.ContractLaws.M.sem-fmap
d_sem'45'fmap_38 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_38 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'fmap_332 v0 v3 v4
-- Once.Lang.ContractLaws.M.sem-para
d_sem'45'para_40 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Lang.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'para_40 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sem'45'para_554 v0 v1 v3 v4
-- Once.Lang.ContractLaws.M.semAnaLayer
d_semAnaLayer_42 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8 ->
  MAlonzo.Code.Once.Lang.Res.T_Res_8
d_semAnaLayer_42 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.Lang.Value.du_semAnaLayer_614 v0 v2 v3
-- Once.Lang.ContractLaws.M.sfmapSemAna
d_sfmapSemAna_44 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Lang.Res.T_Res_8) ->
  AgdaAny -> AgdaAny
d_sfmapSemAna_44 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Lang.Value.du_sfmapSemAna_622 v0 v1 v3 v4
-- Once.Lang.ContractLaws.M.⟦_⟧
d_'10214'_'10215'_46 :: MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_'10214'_'10215'_46 = erased
-- Once.Lang.ContractLaws.M.⟦_⟧F
d_'10214'_'10215'F_48 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> () -> ()
d_'10214'_'10215'F_48 = erased
-- Once.Lang.ContractLaws.M.⟦_⟧ᵍ
d_'10214'_'10215''7501'_50 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> ()
d_'10214'_'10215''7501'_50 = erased
-- Once.Lang.ContractLaws.M.⟦μ⟧
d_'10214'μ'10215'_52 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> ()
d_'10214'μ'10215'_52 = erased
-- Once.Lang.ContractLaws.M.⟦ν⟧
d_'10214'ν'10215'_54 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> ()
d_'10214'ν'10215'_54 = erased
-- Once.Lang.ContractLaws.yes-of
d_yes'45'of_62 ::
  MAlonzo.Code.Once.Lang.Contract.T_Key_56 ->
  [MAlonzo.Code.Once.Lang.Contract.T_Key_56] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_yes'45'of_62 v0 v1 ~v2 = du_yes'45'of_62 v0 v1
du_yes'45'of_62 ::
  MAlonzo.Code.Once.Lang.Contract.T_Key_56 ->
  [MAlonzo.Code.Once.Lang.Contract.T_Key_56] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_yes'45'of_62 v0 v1
  = coe
      du_go_78
      (coe MAlonzo.Code.Once.Lang.Contract.d__'8712'K'63'__108 v0 v1)
-- Once.Lang.ContractLaws._.go
d_go_78 ::
  MAlonzo.Code.Once.Lang.Contract.T_Key_56 ->
  [MAlonzo.Code.Once.Lang.Contract.T_Key_56] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_78 ~v0 ~v1 ~v2 v3 = du_go_78 v3
du_go_78 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_78 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v1 v2
        -> if coe v1
             then case coe v2 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v3
                      -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v2) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.ContractLaws.value-there
d_value'45'there_90 ::
  MAlonzo.Code.Once.Lang.Contract.T_Key_56 ->
  [MAlonzo.Code.Once.Lang.Contract.T_Key_56] ->
  MAlonzo.Code.Once.Lang.Contract.T_Contract_112 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_value'45'there_90 ~v0 ~v1 v2 v3 = du_value'45'there_90 v2 v3
du_value'45'there_90 ::
  MAlonzo.Code.Once.Lang.Contract.T_Contract_112 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_value'45'there_90 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Contract.C_value_114 v2
        -> coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v1
      MAlonzo.Code.Once.Lang.Contract.C_answers_116 v2 -> coe v1
      MAlonzo.Code.Once.Lang.Contract.C_effect_118 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.ContractLaws.answer-there
d_answer'45'there_104 ::
  MAlonzo.Code.Once.Lang.Contract.T_Key_56 ->
  [MAlonzo.Code.Once.Lang.Contract.T_Key_56] ->
  MAlonzo.Code.Once.Lang.Contract.T_Contract_112 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_answer'45'there_104 ~v0 ~v1 v2 v3 = du_answer'45'there_104 v2 v3
du_answer'45'there_104 ::
  MAlonzo.Code.Once.Lang.Contract.T_Contract_112 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_answer'45'there_104 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Contract.C_value_114 v2 -> coe v1
      MAlonzo.Code.Once.Lang.Contract.C_answers_116 v2
        -> coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v1
      MAlonzo.Code.Once.Lang.Contract.C_effect_118 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.ContractLaws.value-∈
d_value'45''8712'_120 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Contract.T_Key_56 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_value'45''8712'_120 v0 ~v1 ~v2 ~v3 v4 ~v5
  = du_value'45''8712'_120 v0 v4
du_value'45''8712'_120 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_value'45''8712'_120 v0 v1
  = case coe v0 of
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v1 of
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v8
                      -> coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v8
                      -> coe
                           du_value'45'there_90
                           (coe
                              MAlonzo.Code.Once.Lang.Contract.d_contractOf_144 (coe v4) (coe v5))
                           (coe du_value'45''8712'_120 (coe v3) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.ContractLaws.answer-∈
d_answer'45''8712'_152 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Contract.T_Key_56 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_answer'45''8712'_152 v0 ~v1 ~v2 ~v3 v4 ~v5
  = du_answer'45''8712'_152 v0 v4
du_answer'45''8712'_152 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_answer'45''8712'_152 v0 v1
  = case coe v0 of
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v1 of
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v8
                      -> coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v8
                      -> coe
                           du_answer'45'there_104
                           (coe
                              MAlonzo.Code.Once.Lang.Contract.d_contractOf_144 (coe v4) (coe v5))
                           (coe du_answer'45''8712'_152 (coe v3) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.ContractLaws.base-contract
d_base'45'contract_180 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_IsBaseType_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_base'45'contract_180 = erased
