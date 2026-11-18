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
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Once.Contract
import qualified MAlonzo.Code.Once.IR.Semantics.Polynomial
import qualified MAlonzo.Code.Once.IR.Semantics.Value
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.Spec.Polynomial
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.ContractLaws.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_6 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_6 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'base'45'to'45'full_422
      v2 v3 v4
-- Once.ContractLaws.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_8 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_8 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'full'45'to'45'base_386
      v1 v2
-- Once.ContractLaws.M.coerce-functor
d_coerce'45'functor_10 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor_10 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'functor_254 v1 v3
-- Once.ContractLaws.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_12 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_12 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'functor'8315''185'_298
      v1 v3
-- Once.ContractLaws.M.coerce-μ-in
d_coerce'45'μ'45'in_14 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_14 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'μ'45'in_456 v1 v3
-- Once.ContractLaws.M.coerce-μ-out
d_coerce'45'μ'45'out_16 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_16 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'μ'45'out_502 v2
      v3 v5
-- Once.ContractLaws.M.coerce-ν-in
d_coerce'45'ν'45'in_18 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_18 v0
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'ν'45'in_618
-- Once.ContractLaws.M.coerce-ν-out
d_coerce'45'ν'45'out_20 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_20 v0 v1 v2
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_coerce'45'ν'45'out_628 v2
-- Once.ContractLaws.M.eraseᵍ
d_erase'7501'_22 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_erase'7501'_22 v0 v1 v2
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_erase'7501'_112 v1 v2
-- Once.ContractLaws.M.sem-CoIn
d_sem'45'CoIn_24 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Polynomial.T_νS_18
d_sem'45'CoIn_24 v0 v1 v2
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'CoIn_648 v1 v2
-- Once.ContractLaws.M.sem-CoOut
d_sem'45'CoOut_26 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.IR.Semantics.Polynomial.T_νS_18 ->
  MAlonzo.Code.Once.Res.T_Res_6
d_sem'45'CoOut_26 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'CoOut_636 v2 v3 v4
-- Once.ContractLaws.M.sem-In
d_sem'45'In_28 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  AgdaAny -> MAlonzo.Code.Once.Spec.Polynomial.T_μS_82
d_sem'45'In_28 v0 v1 v2
  = coe MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'In_544 v1 v2
-- Once.ContractLaws.M.sem-Out
d_sem'45'Out_30 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'Out_30 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'Out_556 v2 v3 v4
-- Once.ContractLaws.M.sem-ana
d_sem'45'ana_32 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  AgdaAny -> MAlonzo.Code.Once.IR.Semantics.Polynomial.T_νS_18
d_sem'45'ana_32 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'ana_660 v0 v1 v3 v4
-- Once.ContractLaws.M.sem-cata
d_sem'45'cata_34 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'cata_34 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'cata_572 v2 v3 v5
-- Once.ContractLaws.M.sem-fmap
d_sem'45'fmap_36 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_36 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'fmap_344 v1 v4 v5
-- Once.ContractLaws.M.sem-para
d_sem'45'para_38 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Spec.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'para_38 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sem'45'para_592 v2 v3 v5 v6
-- Once.ContractLaws.M.semAnaLayer
d_semAnaLayer_40 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Res.T_Res_6 -> MAlonzo.Code.Once.Res.T_Res_6
d_semAnaLayer_40 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_semAnaLayer_668 v0 v1 v3 v4
-- Once.ContractLaws.M.sfmapSemAna
d_sfmapSemAna_42 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) -> AgdaAny -> AgdaAny
d_sfmapSemAna_42 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.IR.Semantics.Value.du_sfmapSemAna_678 v0 v1 v2 v4
      v5
-- Once.ContractLaws.M.⟦_⟧
d_'10214'_'10215'_44 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_'10214'_'10215'_44 = erased
-- Once.ContractLaws.M.⟦_⟧F
d_'10214'_'10215'F_46 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> ()
d_'10214'_'10215'F_46 = erased
-- Once.ContractLaws.M.⟦_⟧ᵍ
d_'10214'_'10215''7501'_48 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_'10214'_'10215''7501'_48 = erased
-- Once.ContractLaws.M.⟦μ⟧
d_'10214'μ'10215'_50 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> ()
d_'10214'μ'10215'_50 = erased
-- Once.ContractLaws.M.⟦ν⟧
d_'10214'ν'10215'_52 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> ()
d_'10214'ν'10215'_52 = erased
-- Once.ContractLaws.yes-of
d_yes'45'of_60 ::
  MAlonzo.Code.Once.Contract.T_Key_54 ->
  [MAlonzo.Code.Once.Contract.T_Key_54] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_yes'45'of_60 v0 v1 ~v2 = du_yes'45'of_60 v0 v1
du_yes'45'of_60 ::
  MAlonzo.Code.Once.Contract.T_Key_54 ->
  [MAlonzo.Code.Once.Contract.T_Key_54] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_yes'45'of_60 v0 v1
  = coe
      du_go_76 (coe MAlonzo.Code.Once.Contract.d__'8712'K'63'__106 v0 v1)
-- Once.ContractLaws._.go
d_go_76 ::
  MAlonzo.Code.Once.Contract.T_Key_54 ->
  [MAlonzo.Code.Once.Contract.T_Key_54] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_76 ~v0 ~v1 ~v2 v3 = du_go_76 v3
du_go_76 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_76 v0
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
d_value'45'there_88 ::
  MAlonzo.Code.Once.Contract.T_Key_54 ->
  [MAlonzo.Code.Once.Contract.T_Key_54] ->
  MAlonzo.Code.Once.Contract.T_Contract_110 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_value'45'there_88 ~v0 ~v1 v2 v3 = du_value'45'there_88 v2 v3
du_value'45'there_88 ::
  MAlonzo.Code.Once.Contract.T_Contract_110 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_value'45'there_88 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Contract.C_value_112 v2
        -> coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v1
      MAlonzo.Code.Once.Contract.C_answers_114 v2 -> coe v1
      MAlonzo.Code.Once.Contract.C_effect_116 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.ContractLaws.answer-there
d_answer'45'there_102 ::
  MAlonzo.Code.Once.Contract.T_Key_54 ->
  [MAlonzo.Code.Once.Contract.T_Key_54] ->
  MAlonzo.Code.Once.Contract.T_Contract_110 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_answer'45'there_102 ~v0 ~v1 v2 v3 = du_answer'45'there_102 v2 v3
du_answer'45'there_102 ::
  MAlonzo.Code.Once.Contract.T_Contract_110 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_answer'45'there_102 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Contract.C_value_112 v2 -> coe v1
      MAlonzo.Code.Once.Contract.C_answers_114 v2
        -> coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v1
      MAlonzo.Code.Once.Contract.C_effect_116 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.ContractLaws.value-∈
d_value'45''8712'_118 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Contract.T_Key_54 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_value'45''8712'_118 v0 ~v1 ~v2 ~v3 v4 ~v5
  = du_value'45''8712'_118 v0 v4
du_value'45''8712'_118 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_value'45''8712'_118 v0 v1
  = case coe v0 of
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v1 of
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v8
                      -> coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v8
                      -> coe
                           du_value'45'there_88
                           (coe MAlonzo.Code.Once.Contract.d_contractOf_142 (coe v4) (coe v5))
                           (coe du_value'45''8712'_118 (coe v3) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.ContractLaws.answer-∈
d_answer'45''8712'_150 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Contract.T_Key_54 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_answer'45''8712'_150 v0 ~v1 ~v2 ~v3 v4 ~v5
  = du_answer'45''8712'_150 v0 v4
du_answer'45''8712'_150 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_answer'45''8712'_150 v0 v1
  = case coe v0 of
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v1 of
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v8
                      -> coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v8
                      -> coe
                           du_answer'45'there_102
                           (coe MAlonzo.Code.Once.Contract.d_contractOf_142 (coe v4) (coe v5))
                           (coe du_answer'45''8712'_150 (coe v3) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.ContractLaws.base-contract
d_base'45'contract_178 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_base'45'contract_178 = erased
