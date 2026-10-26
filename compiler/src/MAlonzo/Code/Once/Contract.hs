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

module MAlonzo.Code.Once.Contract where

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
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Membership.DecSetoid
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Internal.Event
import qualified MAlonzo.Code.Once.Internal.Polynomial
import qualified MAlonzo.Code.Once.Internal.Value
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Type.Core
import qualified MAlonzo.Code.Once.Type.DecEq
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Contract.M.coerce-base-to-full
d_coerce'45'base'45'to'45'full_6 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 -> AgdaAny -> AgdaAny
d_coerce'45'base'45'to'45'full_6 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'base'45'to'45'full_420
      v2 v3 v4
-- Once.Contract.M.coerce-full-to-base
d_coerce'45'full'45'to'45'base_8 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'full'45'to'45'base_8 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'full'45'to'45'base_384
      v1 v2
-- Once.Contract.M.coerce-functor
d_coerce'45'functor_10 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor_10 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'functor_252 v1 v3
-- Once.Contract.M.coerce-functor⁻¹
d_coerce'45'functor'8315''185'_12 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_coerce'45'functor'8315''185'_12 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'functor'8315''185'_296
      v1 v3
-- Once.Contract.M.coerce-μ-in
d_coerce'45'μ'45'in_14 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'in_14 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'in_454 v1 v3
-- Once.Contract.M.coerce-μ-out
d_coerce'45'μ'45'out_16 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 -> () -> AgdaAny -> AgdaAny
d_coerce'45'μ'45'out_16 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Internal.Value.du_coerce'45'μ'45'out_500 v2 v3 v5
-- Once.Contract.M.coerce-ν-in
d_coerce'45'ν'45'in_18 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'in_18 v0
  = coe MAlonzo.Code.Once.Internal.Value.du_coerce'45'ν'45'in_616
-- Once.Contract.M.coerce-ν-out
d_coerce'45'ν'45'out_20 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 -> () -> AgdaAny -> AgdaAny
d_coerce'45'ν'45'out_20 v0 v1 v2
  = coe MAlonzo.Code.Once.Internal.Value.du_coerce'45'ν'45'out_626 v2
-- Once.Contract.M.eraseᵍ
d_erase'7501'_22 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> AgdaAny -> AgdaAny
d_erase'7501'_22 v0 v1 v2
  = coe MAlonzo.Code.Once.Internal.Value.du_erase'7501'_110 v1 v2
-- Once.Contract.M.sem-CoIn
d_sem'45'CoIn_24 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Polynomial.T_νS_98
d_sem'45'CoIn_24 v0 v1 v2
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'CoIn_646 v1 v2
-- Once.Contract.M.sem-CoOut
d_sem'45'CoOut_26 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_νS_98 ->
  MAlonzo.Code.Once.Res.T_Res_6
d_sem'45'CoOut_26 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'CoOut_634 v2 v3 v4
-- Once.Contract.M.sem-In
d_sem'45'In_28 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Polynomial.T_μS_82
d_sem'45'In_28 v0 v1 v2
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'In_542 v1 v2
-- Once.Contract.M.sem-Out
d_sem'45'Out_30 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'Out_30 v0 v1 v2 v3 v4
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'Out_554 v2 v3 v4
-- Once.Contract.M.sem-ana
d_sem'45'ana_32 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Polynomial.T_νS_98
d_sem'45'ana_32 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Internal.Value.du_sem'45'ana_658 v0 v1 v3 v4
-- Once.Contract.M.sem-cata
d_sem'45'cata_34 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'cata_34 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'cata_570 v2 v3 v5
-- Once.Contract.M.sem-fmap
d_sem'45'fmap_36 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_sem'45'fmap_36 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.Internal.Value.du_sem'45'fmap_342 v1 v4 v5
-- Once.Contract.M.sem-para
d_sem'45'para_38 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_WFFun_118 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Once.Internal.Polynomial.T_μS_82 -> AgdaAny
d_sem'45'para_38 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.Internal.Value.du_sem'45'para_590 v2 v3 v5 v6
-- Once.Contract.M.semAnaLayer
d_semAnaLayer_40 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Res.T_Res_6 -> MAlonzo.Code.Once.Res.T_Res_6
d_semAnaLayer_40 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Internal.Value.du_semAnaLayer_666 v0 v1 v3 v4
-- Once.Contract.M.sfmapSemAna
d_sfmapSemAna_42 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Internal.Polynomial.T_SFunctor_6 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) -> AgdaAny -> AgdaAny
d_sfmapSemAna_42 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Internal.Value.du_sfmapSemAna_676 v0 v1 v2 v4 v5
-- Once.Contract.M.⟦_⟧
d_'10214'_'10215'_44 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_'10214'_'10215'_44 = erased
-- Once.Contract.M.⟦_⟧F
d_'10214'_'10215'F_46 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> () -> ()
d_'10214'_'10215'F_46 = erased
-- Once.Contract.M.⟦_⟧ᵍ
d_'10214'_'10215''7501'_48 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_'10214'_'10215''7501'_48 = erased
-- Once.Contract.M.⟦μ⟧
d_'10214'μ'10215'_50 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> ()
d_'10214'μ'10215'_50 = erased
-- Once.Contract.M.⟦ν⟧
d_'10214'ν'10215'_52 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> ()
d_'10214'ν'10215'_52 = erased
-- Once.Contract.Key
d_Key_54 = ()
data T_Key_54
  = C_key_68 MAlonzo.Code.Agda.Builtin.String.T_String_6
             MAlonzo.Code.Once.Spec.Type.T_Ty_8
             MAlonzo.Code.Once.Spec.Type.T_Ty_8
-- Once.Contract.Key.kname
d_kname_62 ::
  T_Key_54 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_kname_62 v0
  = case coe v0 of
      C_key_68 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Contract.Key.kdom
d_kdom_64 :: T_Key_54 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_kdom_64 v0
  = case coe v0 of
      C_key_68 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Contract.Key.kcod
d_kcod_66 :: T_Key_54 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_kcod_66 v0
  = case coe v0 of
      C_key_68 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Contract._≟K_
d__'8799'K__70 ::
  T_Key_54 ->
  T_Key_54 -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'K__70 v0 v1
  = case coe v0 of
      C_key_68 v2 v3 v4
        -> case coe v1 of
             C_key_68 v5 v6 v7
               -> coe
                    du_go_88
                    (coe
                       MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v2)
                       (coe v5))
                    (coe
                       MAlonzo.Code.Once.Type.DecEq.d__'8799'T__228 (coe (0 :: Integer))
                       (coe v3) (coe v6))
                    (coe
                       MAlonzo.Code.Once.Type.DecEq.d__'8799'T__228 (coe (0 :: Integer))
                       (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Contract._.go
d_go_88 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_go_88 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 = du_go_88 v6 v7 v8
du_go_88 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_go_88 v0 v1 v2
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
-- Once.Contract._∈K?_
d__'8712'K'63'__106 ::
  T_Key_54 ->
  [T_Key_54] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8712'K'63'__106
  = coe
      MAlonzo.Code.Data.List.Membership.DecSetoid.du__'8712''63'__60
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
         (coe d__'8799'K__70))
-- Once.Contract.ISig
d_ISig_108 :: ()
d_ISig_108 = erased
-- Once.Contract.Contract
d_Contract_110 = ()
data T_Contract_110
  = C_value_112 T_Key_54 | C_answers_114 T_Key_54 | C_effect_116
-- Once.Contract.contract-eff
d_contract'45'eff_122 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Contract_110
d_contract'45'eff_122 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
        -> if coe v5
             then coe seq (coe v6) (coe C_effect_116)
             else coe
                    seq (coe v6)
                    (case coe v4 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                         -> if coe v7
                              then coe seq (coe v8) (coe C_effect_116)
                              else coe
                                     seq (coe v8)
                                     (coe C_answers_114 (coe C_key_68 (coe v0) (coe v1) (coe v2)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Contract.contractOf
d_contractOf_142 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_Contract_110
d_contractOf_142 v0 v1
  = let v2
          = coe
              C_value_112
              (coe
                 C_key_68 (coe v0) (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                 (coe v1)) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v3 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v6 v7
                  -> case coe v6 of
                       MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                         -> case coe v7 of
                              MAlonzo.Code.Once.Spec.Grade.C_fin_42 v8
                                -> case coe v8 of
                                     MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                                       -> coe
                                            C_value_112
                                            (coe
                                               C_key_68 (coe v0)
                                               (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18) (coe v5))
                                     MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                       -> coe
                                            d_contract'45'eff_122 (coe v0)
                                            (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18) (coe v5)
                                            (coe
                                               MAlonzo.Code.Once.Type.Core.du_isVoid'63'_58
                                               (coe v5))
                                            (coe
                                               MAlonzo.Code.Once.Type.Core.du_isUnit'63'_64
                                               (coe v5))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                -> coe
                                     d_contract'45'eff_122 (coe v0)
                                     (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18) (coe v5)
                                     (coe MAlonzo.Code.Once.Type.Core.du_isVoid'63'_58 (coe v5))
                                     (coe MAlonzo.Code.Once.Type.Core.du_isUnit'63'_64 (coe v5))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Once.Spec.Grade.C_One_10
                         -> case coe v7 of
                              MAlonzo.Code.Once.Spec.Grade.C_fin_42 v8
                                -> case coe v8 of
                                     MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                                       -> coe C_value_112 (coe C_key_68 (coe v0) (coe v3) (coe v5))
                                     MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                       -> coe
                                            d_contract'45'eff_122 (coe v0) (coe v3) (coe v5)
                                            (coe
                                               MAlonzo.Code.Once.Type.Core.du_isVoid'63'_58
                                               (coe v5))
                                            (coe
                                               MAlonzo.Code.Once.Type.Core.du_isUnit'63'_64
                                               (coe v5))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                -> coe
                                     d_contract'45'eff_122 (coe v0) (coe v3) (coe v5)
                                     (coe MAlonzo.Code.Once.Type.Core.du_isVoid'63'_58 (coe v5))
                                     (coe MAlonzo.Code.Once.Type.Core.du_isUnit'63'_64 (coe v5))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Once.Spec.Grade.C_Many_12
                         -> case coe v7 of
                              MAlonzo.Code.Once.Spec.Grade.C_fin_42 v8
                                -> case coe v8 of
                                     MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36
                                       -> coe C_value_112 (coe C_key_68 (coe v0) (coe v3) (coe v5))
                                     MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                       -> coe
                                            d_contract'45'eff_122 (coe v0) (coe v3) (coe v5)
                                            (coe
                                               MAlonzo.Code.Once.Type.Core.du_isVoid'63'_58
                                               (coe v5))
                                            (coe
                                               MAlonzo.Code.Once.Type.Core.du_isUnit'63'_64
                                               (coe v5))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                -> coe
                                     d_contract'45'eff_122 (coe v0) (coe v3) (coe v5)
                                     (coe MAlonzo.Code.Once.Type.Core.du_isVoid'63'_58 (coe v5))
                                     (coe MAlonzo.Code.Once.Type.Core.du_isUnit'63'_64 (coe v5))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v2)
-- Once.Contract.value-step
d_value'45'step_202 :: T_Contract_110 -> [T_Key_54] -> [T_Key_54]
d_value'45'step_202 v0 v1
  = case coe v0 of
      C_value_112 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2) (coe v1)
      C_answers_114 v2 -> coe v1
      C_effect_116 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Contract.answer-step
d_answer'45'step_204 :: T_Contract_110 -> [T_Key_54] -> [T_Key_54]
d_answer'45'step_204 v0 v1
  = case coe v0 of
      C_value_112 v2 -> coe v1
      C_answers_114 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2) (coe v1)
      C_effect_116 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Contract.valueKeys
d_valueKeys_222 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> [T_Key_54]
d_valueKeys_222 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    d_value'45'step_202 (coe d_contractOf_142 (coe v3) (coe v4))
                    (coe d_valueKeys_222 (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Contract.answerKeys
d_answerKeys_224 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> [T_Key_54]
d_answerKeys_224 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    d_answer'45'step_204 (coe d_contractOf_142 (coe v3) (coe v4))
                    (coe d_answerKeys_224 (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Contract.Impl
d_Impl_240 a0 = ()
data T_Impl_240
  = C_constructor_260 ([MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
                       T_Key_54 ->
                       MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
                       AgdaAny -> AgdaAny)
                      (T_Key_54 ->
                       MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
                       AgdaAny -> AgdaAny)
-- Once.Contract.Impl.answerI
d_answerI_254 ::
  T_Impl_240 ->
  [MAlonzo.Code.Once.Internal.Event.T_SigOpEvent_56] ->
  T_Key_54 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny -> AgdaAny
d_answerI_254 v0
  = case coe v0 of
      C_constructor_260 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Contract.Impl.pureI
d_pureI_258 ::
  T_Impl_240 ->
  T_Key_54 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny -> AgdaAny
d_pureI_258 v0
  = case coe v0 of
      C_constructor_260 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Contract.valueOf-at
d_valueOf'45'at_266 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_Impl_240 ->
  T_Key_54 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny
d_valueOf'45'at_266 ~v0 v1 v2 ~v3 v4
  = du_valueOf'45'at_266 v1 v2 v4
du_valueOf'45'at_266 ::
  T_Impl_240 ->
  T_Key_54 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny
du_valueOf'45'at_266 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then case coe v4 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v5
                      -> coe d_pureI_258 v0 v1 v5
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v4) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Contract.valueOf
d_valueOf_288 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_Impl_240 ->
  T_Key_54 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny -> AgdaAny
d_valueOf_288 v0 v1 v2 ~v3 = du_valueOf_288 v0 v1 v2
du_valueOf_288 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  T_Impl_240 -> T_Key_54 -> AgdaAny -> AgdaAny
du_valueOf_288 v0 v1 v2
  = coe
      du_valueOf'45'at_266 (coe v1) (coe v2)
      (coe d__'8712'K'63'__106 v2 (d_valueKeys_222 (coe v0)))
