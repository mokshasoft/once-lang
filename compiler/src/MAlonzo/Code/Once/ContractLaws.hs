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

module MAlonzo.Code.Once.ContractLaws where

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
import qualified MAlonzo.Code.Once.Contract
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.ContractLaws.yes-of
d_yes'45'of_10 ::
  MAlonzo.Code.Once.Contract.T_Key_54 ->
  [MAlonzo.Code.Once.Contract.T_Key_54] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_yes'45'of_10 v0 v1 ~v2 = du_yes'45'of_10 v0 v1
du_yes'45'of_10 ::
  MAlonzo.Code.Once.Contract.T_Key_54 ->
  [MAlonzo.Code.Once.Contract.T_Key_54] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_yes'45'of_10 v0 v1
  = coe
      du_go_26 (coe MAlonzo.Code.Once.Contract.d__'8712'K'63'__106 v0 v1)
-- Once.ContractLaws._.go
d_go_26 ::
  MAlonzo.Code.Once.Contract.T_Key_54 ->
  [MAlonzo.Code.Once.Contract.T_Key_54] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_26 ~v0 ~v1 ~v2 v3 = du_go_26 v3
du_go_26 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_26 v0
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
-- Once.ContractLaws.value-there
d_value'45'there_38 ::
  MAlonzo.Code.Once.Contract.T_Key_54 ->
  [MAlonzo.Code.Once.Contract.T_Key_54] ->
  MAlonzo.Code.Once.Contract.T_Contract_110 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_value'45'there_38 ~v0 ~v1 v2 v3 = du_value'45'there_38 v2 v3
du_value'45'there_38 ::
  MAlonzo.Code.Once.Contract.T_Contract_110 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_value'45'there_38 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Contract.C_value_112 v2
        -> coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v1
      MAlonzo.Code.Once.Contract.C_answers_114 v2 -> coe v1
      MAlonzo.Code.Once.Contract.C_effect_116 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.ContractLaws.answer-there
d_answer'45'there_52 ::
  MAlonzo.Code.Once.Contract.T_Key_54 ->
  [MAlonzo.Code.Once.Contract.T_Key_54] ->
  MAlonzo.Code.Once.Contract.T_Contract_110 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_answer'45'there_52 ~v0 ~v1 v2 v3 = du_answer'45'there_52 v2 v3
du_answer'45'there_52 ::
  MAlonzo.Code.Once.Contract.T_Contract_110 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_answer'45'there_52 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Contract.C_value_112 v2 -> coe v1
      MAlonzo.Code.Once.Contract.C_answers_114 v2
        -> coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v1
      MAlonzo.Code.Once.Contract.C_effect_116 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.ContractLaws.value-∈
d_value'45''8712'_68 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Contract.T_Key_54 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_value'45''8712'_68 v0 ~v1 ~v2 ~v3 v4 ~v5
  = du_value'45''8712'_68 v0 v4
du_value'45''8712'_68 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_value'45''8712'_68 v0 v1
  = case coe v0 of
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v1 of
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v8
                      -> coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v8
                      -> coe
                           du_value'45'there_38
                           (coe MAlonzo.Code.Once.Contract.d_contractOf_142 (coe v4) (coe v5))
                           (coe du_value'45''8712'_68 (coe v3) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.ContractLaws.answer-∈
d_answer'45''8712'_100 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Contract.T_Key_54 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_answer'45''8712'_100 v0 ~v1 ~v2 ~v3 v4 ~v5
  = du_answer'45''8712'_100 v0 v4
du_answer'45''8712'_100 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_answer'45''8712'_100 v0 v1
  = case coe v0 of
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v1 of
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v8
                      -> coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v8
                      -> coe
                           du_answer'45'there_52
                           (coe MAlonzo.Code.Once.Contract.d_contractOf_142 (coe v4) (coe v5))
                           (coe du_answer'45''8712'_100 (coe v3) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.ContractLaws.base-contract
d_base'45'contract_128 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_base'45'contract_128 = erased
