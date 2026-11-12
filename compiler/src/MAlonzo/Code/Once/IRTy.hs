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

module MAlonzo.Code.Once.IRTy where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Type.DecEq
import qualified MAlonzo.Code.Once.Type.Grade
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.IRTy.IRFunctor
d_IRFunctor_4 = ()
data T_IRFunctor_4
  = C_K_8 T_IRTy_6 | C_Id_10 |
    C__'8853'__12 T_IRFunctor_4 T_IRFunctor_4 |
    C__'8855'__14 T_IRFunctor_4 T_IRFunctor_4
-- Once.IRTy.IRTy
d_IRTy_6 = ()
data T_IRTy_6
  = C_Unit_16 | C_Void_18 | C__'42'__20 T_IRTy_6 T_IRTy_6 |
    C__'43'__22 T_IRTy_6 T_IRTy_6 |
    C__'8667''91'_'93'__24 T_IRTy_6
                           MAlonzo.Code.Once.Spec.Grade.T_Purity_40 T_IRTy_6 |
    C_μ'45'type_26 T_IRFunctor_4 | C_ν'45'type_28 T_IRFunctor_4 |
    C_Int_30 | C_Float_32
-- Once.IRTy.eraseArrow
d_eraseArrow_34 ::
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  T_IRTy_6 -> T_IRTy_6 -> T_IRTy_6
d_eraseArrow_34 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_Zero_8
        -> coe C__'8667''91'_'93'__24 (coe C_Unit_16) (coe v1) (coe v3)
      MAlonzo.Code.Once.Spec.Grade.C_One_10
        -> coe C__'8667''91'_'93'__24 (coe v2) (coe v1) (coe v3)
      MAlonzo.Code.Once.Spec.Grade.C_Many_12
        -> coe C__'8667''91'_'93'__24 (coe v2) (coe v1) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRTy.⌊_⌋
d_'8970'_'8971'_56 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> T_IRTy_6
d_'8970'_'8971'_56 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.C_var_16 v2 -> coe C_Void_18
      MAlonzo.Code.Once.Spec.Type.C_Unit_18 -> coe C_Unit_16
      MAlonzo.Code.Once.Spec.Type.C_Void_20 -> coe C_Void_18
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v2 v3
        -> coe
             C__'42'__20 (coe d_'8970'_'8971'_56 (coe v0) (coe v2))
             (coe d_'8970'_'8971'_56 (coe v0) (coe v3))
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v2 v3
        -> coe
             C__'43'__22 (coe d_'8970'_'8971'_56 (coe v0) (coe v2))
             (coe d_'8970'_'8971'_56 (coe v0) (coe v3))
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v2 v3 v4
        -> coe
             d_eraseArrow_34
             (coe MAlonzo.Code.Once.Spec.Grade.d_quantity_86 (coe v3))
             (coe MAlonzo.Code.Once.Spec.Grade.d_purity_88 (coe v3))
             (coe d_'8970'_'8971'_56 (coe v0) (coe v2))
             (coe d_'8970'_'8971'_56 (coe v0) (coe v4))
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v2
        -> coe C_μ'45'type_26 (coe d_eraseF_60 (coe v0) (coe v2))
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v2 v3
        -> coe C_ν'45'type_28 (coe d_eraseF_60 (coe v0) (coe v2))
      MAlonzo.Code.Once.Spec.Type.C_Int_32 -> coe C_Int_30
      MAlonzo.Code.Once.Spec.Type.C_Float_34 -> coe C_Float_32
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRTy.eraseF
d_eraseF_60 ::
  Integer -> MAlonzo.Code.Once.Spec.Type.T_Fun_12 -> T_IRFunctor_4
d_eraseF_60 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.C_K_38 v2
        -> coe C_K_8 (coe d_'8970'_'8971'_56 (coe v0) (coe v2))
      MAlonzo.Code.Once.Spec.Type.C_Id_40 -> coe C_Id_10
      MAlonzo.Code.Once.Spec.Type.C__'8853'__42 v2 v3
        -> coe
             C__'8853'__12 (coe d_eraseF_60 (coe v0) (coe v2))
             (coe d_eraseF_60 (coe v0) (coe v3))
      MAlonzo.Code.Once.Spec.Type.C__'8855'__44 v2 v3
        -> coe
             C__'8855'__14 (coe d_eraseF_60 (coe v0) (coe v2))
             (coe d_eraseF_60 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRTy.⟦_⟧TI
d_'10214'_'10215'TI_90 :: T_IRFunctor_4 -> T_IRTy_6 -> T_IRTy_6
d_'10214'_'10215'TI_90 v0 v1
  = case coe v0 of
      C_K_8 v2 -> coe v2
      C_Id_10 -> coe v1
      C__'8853'__12 v2 v3
        -> coe
             C__'43'__22 (coe d_'10214'_'10215'TI_90 (coe v2) (coe v1))
             (coe d_'10214'_'10215'TI_90 (coe v3) (coe v1))
      C__'8855'__14 v2 v3
        -> coe
             C__'42'__20 (coe d_'10214'_'10215'TI_90 (coe v2) (coe v1))
             (coe d_'10214'_'10215'TI_90 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRTy.IsBaseTypeI
d_IsBaseTypeI_110 a0 = ()
data T_IsBaseTypeI_110
  = C_base'45'Unit_112 | C_base'45'Void_114 | C_base'45'Int_116 |
    C_base'45'Float_118 |
    C_base'45'Prod_124 T_IsBaseTypeI_110 T_IsBaseTypeI_110 |
    C_base'45'Sum_130 T_IsBaseTypeI_110 T_IsBaseTypeI_110
-- Once.IRTy.WellFormedFI
d_WellFormedFI_132 a0 = ()
data T_WellFormedFI_132
  = C_wf'45'K_136 T_IsBaseTypeI_110 | C_wf'45'Id_138 |
    C_wf'45'Sum_144 T_WellFormedFI_132 T_WellFormedFI_132 |
    C_wf'45'Prod_150 T_WellFormedFI_132 T_WellFormedFI_132
-- Once.IRTy.IsBaseTypeI-irrelevant
d_IsBaseTypeI'45'irrelevant_158 ::
  T_IRTy_6 ->
  T_IsBaseTypeI_110 ->
  T_IsBaseTypeI_110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_IsBaseTypeI'45'irrelevant_158 = erased
-- Once.IRTy.WellFormedFI-irrelevant
d_WellFormedFI'45'irrelevant_182 ::
  T_IRFunctor_4 ->
  T_WellFormedFI_132 ->
  T_WellFormedFI_132 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_WellFormedFI'45'irrelevant_182 = erased
-- Once.IRTy.irtyTag
d_irtyTag_204 :: T_IRTy_6 -> Integer
d_irtyTag_204 v0
  = case coe v0 of
      C_Unit_16 -> coe (0 :: Integer)
      C_Void_18 -> coe (1 :: Integer)
      C__'42'__20 v1 v2 -> coe (2 :: Integer)
      C__'43'__22 v1 v2 -> coe (3 :: Integer)
      C__'8667''91'_'93'__24 v1 v2 v3 -> coe (4 :: Integer)
      C_μ'45'type_26 v1 -> coe (5 :: Integer)
      C_ν'45'type_28 v1 -> coe (6 :: Integer)
      C_Int_30 -> coe (7 :: Integer)
      C_Float_32 -> coe (8 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRTy._≟IRTy_
d__'8799'IRTy__206 ::
  T_IRTy_6 ->
  T_IRTy_6 -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'IRTy__206 v0 v1
  = coe
      d_'8799'IRTy'45'aux_212 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796
         (coe d_irtyTag_204 (coe v0)) (coe d_irtyTag_204 (coe v1)))
-- Once.IRTy.≟IRTy-aux
d_'8799'IRTy'45'aux_212 ::
  T_IRTy_6 ->
  T_IRTy_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRTy'45'aux_212 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4) (coe du_'8799'IRTy'45'diag_218 (coe v0) (coe v1))
             else coe
                    seq (coe v4)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v3)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRTy.≟IRTy-diag
d_'8799'IRTy'45'diag_218 ::
  T_IRTy_6 ->
  T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRTy'45'diag_218 v0 v1 ~v2
  = du_'8799'IRTy'45'diag_218 v0 v1
du_'8799'IRTy'45'diag_218 ::
  T_IRTy_6 ->
  T_IRTy_6 -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRTy'45'diag_218 v0 v1
  = case coe v0 of
      C_Unit_16
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      C_Void_18
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      C__'42'__20 v2 v3
        -> case coe v1 of
             C__'42'__20 v4 v5
               -> let v6
                        = d_'8799'IRTy'45'aux_212
                            (coe v2) (coe v4)
                            (coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v6 ->
                                  coe
                                    MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                    (coe d_irtyTag_204 (coe v2)))
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                  (coe
                                     eqInt (coe d_irtyTag_204 (coe v2))
                                     (coe d_irtyTag_204 (coe v4)))
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                     (coe
                                        eqInt (coe d_irtyTag_204 (coe v2))
                                        (coe d_irtyTag_204 (coe v4)))))) in
                  coe
                    (let v7
                           = d_'8799'IRTy'45'aux_212
                               (coe v3) (coe v5)
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                  erased
                                  (\ v7 ->
                                     coe
                                       MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                       (coe d_irtyTag_204 (coe v3)))
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                     (coe
                                        eqInt (coe d_irtyTag_204 (coe v3))
                                        (coe d_irtyTag_204 (coe v5)))
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                        (coe
                                           eqInt (coe d_irtyTag_204 (coe v3))
                                           (coe d_irtyTag_204 (coe v5)))))) in
                     coe
                       (let v8
                              = case coe v7 of
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                    -> coe
                                         seq (coe v8)
                                         (coe
                                            seq (coe v9)
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                               (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                                  _ -> MAlonzo.RTE.mazUnreachableError in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                               -> let v11
                                        = case coe v7 of
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                              -> case coe v11 of
                                                   MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                     -> case coe v12 of
                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                            -> coe
                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                 (coe v11)
                                                                 (coe
                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                          _ -> coe v8
                                                   _ -> coe v8
                                            _ -> MAlonzo.RTE.mazUnreachableError in
                                  coe
                                    (if coe v9
                                       then case coe v10 of
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v12
                                                -> case coe v7 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                       -> case coe v13 of
                                                            MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                              -> case coe v14 of
                                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                                                                     -> coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                          (coe v13)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                             erased)
                                                                   _ -> coe v11
                                                            _ -> coe v11
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> coe v11
                                       else (case coe v10 of
                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                 -> coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v9)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                               _ -> coe v11))
                             _ -> MAlonzo.RTE.mazUnreachableError)))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'43'__22 v2 v3
        -> case coe v1 of
             C__'43'__22 v4 v5
               -> let v6
                        = d_'8799'IRTy'45'aux_212
                            (coe v2) (coe v4)
                            (coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v6 ->
                                  coe
                                    MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                    (coe d_irtyTag_204 (coe v2)))
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                  (coe
                                     eqInt (coe d_irtyTag_204 (coe v2))
                                     (coe d_irtyTag_204 (coe v4)))
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                     (coe
                                        eqInt (coe d_irtyTag_204 (coe v2))
                                        (coe d_irtyTag_204 (coe v4)))))) in
                  coe
                    (let v7
                           = d_'8799'IRTy'45'aux_212
                               (coe v3) (coe v5)
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                  erased
                                  (\ v7 ->
                                     coe
                                       MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                       (coe d_irtyTag_204 (coe v3)))
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                     (coe
                                        eqInt (coe d_irtyTag_204 (coe v3))
                                        (coe d_irtyTag_204 (coe v5)))
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                        (coe
                                           eqInt (coe d_irtyTag_204 (coe v3))
                                           (coe d_irtyTag_204 (coe v5)))))) in
                     coe
                       (let v8
                              = case coe v7 of
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                    -> coe
                                         seq (coe v8)
                                         (coe
                                            seq (coe v9)
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                               (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                                  _ -> MAlonzo.RTE.mazUnreachableError in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                               -> let v11
                                        = case coe v7 of
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                              -> case coe v11 of
                                                   MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                     -> case coe v12 of
                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                            -> coe
                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                 (coe v11)
                                                                 (coe
                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                          _ -> coe v8
                                                   _ -> coe v8
                                            _ -> MAlonzo.RTE.mazUnreachableError in
                                  coe
                                    (if coe v9
                                       then case coe v10 of
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v12
                                                -> case coe v7 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                       -> case coe v13 of
                                                            MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                              -> case coe v14 of
                                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                                                                     -> coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                          (coe v13)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                             erased)
                                                                   _ -> coe v11
                                                            _ -> coe v11
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> coe v11
                                       else (case coe v10 of
                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                 -> coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v9)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                               _ -> coe v11))
                             _ -> MAlonzo.RTE.mazUnreachableError)))
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'8667''91'_'93'__24 v2 v3 v4
        -> case coe v1 of
             C__'8667''91'_'93'__24 v5 v6 v7
               -> let v8
                        = d_'8799'IRTy'45'aux_212
                            (coe v2) (coe v5)
                            (coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v8 ->
                                  coe
                                    MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                    (coe d_irtyTag_204 (coe v2)))
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                  (coe
                                     eqInt (coe d_irtyTag_204 (coe v2))
                                     (coe d_irtyTag_204 (coe v5)))
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                     (coe
                                        eqInt (coe d_irtyTag_204 (coe v2))
                                        (coe d_irtyTag_204 (coe v5)))))) in
                  coe
                    (let v9
                           = MAlonzo.Code.Once.Type.DecEq.d__'8799'p__10 (coe v3) (coe v6) in
                     coe
                       (let v10
                              = d_'8799'IRTy'45'aux_212
                                  (coe v4) (coe v7)
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                     erased
                                     (\ v10 ->
                                        coe
                                          MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                          (coe d_irtyTag_204 (coe v4)))
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe
                                           eqInt (coe d_irtyTag_204 (coe v4))
                                           (coe d_irtyTag_204 (coe v7)))
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                           (coe
                                              eqInt (coe d_irtyTag_204 (coe v4))
                                              (coe d_irtyTag_204 (coe v7)))))) in
                        coe
                          (let v11
                                 = let v11
                                         = case coe v10 of
                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                               -> coe
                                                    seq (coe v11)
                                                    (coe
                                                       seq (coe v12)
                                                       (coe
                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                                          (coe
                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                                             _ -> MAlonzo.RTE.mazUnreachableError in
                                   coe
                                     (case coe v9 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                          -> case coe v12 of
                                               MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                 -> case coe v13 of
                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                        -> coe
                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                             (coe v12)
                                                             (coe
                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                      _ -> coe v11
                                               _ -> coe v11
                                        _ -> MAlonzo.RTE.mazUnreachableError) in
                           coe
                             (case coe v8 of
                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                  -> let v14
                                           = let v14
                                                   = case coe v10 of
                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                         -> case coe v14 of
                                                              MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                                -> case coe v15 of
                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                       -> coe
                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                            (coe v14)
                                                                            (coe
                                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                     _ -> coe v11
                                                              _ -> coe v11
                                                       _ -> MAlonzo.RTE.mazUnreachableError in
                                             coe
                                               (case coe v9 of
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                                    -> case coe v15 of
                                                         MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                           -> case coe v16 of
                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                  -> coe
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                       (coe v15)
                                                                       (coe
                                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                _ -> coe v14
                                                         _ -> coe v14
                                                  _ -> MAlonzo.RTE.mazUnreachableError) in
                                     coe
                                       (if coe v12
                                          then case coe v13 of
                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                                                   -> case coe v9 of
                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                          -> case coe v16 of
                                                               MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                 -> case coe v17 of
                                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v18
                                                                        -> case coe v10 of
                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v19 v20
                                                                               -> case coe v19 of
                                                                                    MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                                      -> case coe
                                                                                                v20 of
                                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v21
                                                                                             -> coe
                                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                  (coe
                                                                                                     v19)
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                     erased)
                                                                                           _ -> coe
                                                                                                  v14
                                                                                    _ -> coe v14
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      _ -> coe v14
                                                               _ -> coe v14
                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                 _ -> coe v14
                                          else (case coe v13 of
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                    -> coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                         (coe v12)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                  _ -> coe v14))
                                _ -> MAlonzo.RTE.mazUnreachableError))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_μ'45'type_26 v2
        -> case coe v1 of
             C_μ'45'type_26 v3
               -> let v4 = d__'8799'IRFun__220 (coe v2) (coe v3) in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                         -> if coe v5
                              then coe
                                     seq (coe v6)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v5)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           erased))
                              else coe
                                     seq (coe v6)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v5)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_ν'45'type_28 v2
        -> case coe v1 of
             C_ν'45'type_28 v3
               -> let v4 = d__'8799'IRFun__220 (coe v2) (coe v3) in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                         -> if coe v5
                              then coe
                                     seq (coe v6)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v5)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           erased))
                              else coe
                                     seq (coe v6)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v5)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Int_30
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      C_Float_32
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRTy._≟IRFun_
d__'8799'IRFun__220 ::
  T_IRFunctor_4 ->
  T_IRFunctor_4 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'IRFun__220 v0 v1
  = case coe v0 of
      C_K_8 v2
        -> case coe v1 of
             C_K_8 v3
               -> let v4
                        = d_'8799'IRTy'45'aux_212
                            (coe v2) (coe v3)
                            (coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v4 ->
                                  coe
                                    MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                    (coe d_irtyTag_204 (coe v2)))
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                  (coe
                                     eqInt (coe d_irtyTag_204 (coe v2))
                                     (coe d_irtyTag_204 (coe v3)))
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                     (coe
                                        eqInt (coe d_irtyTag_204 (coe v2))
                                        (coe d_irtyTag_204 (coe v3)))))) in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                         -> if coe v5
                              then coe
                                     seq (coe v6)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v5)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                           erased))
                              else coe
                                     seq (coe v6)
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                        (coe v5)
                                        (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             C_Id_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C__'8853'__12 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C__'8855'__14 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Id_10
        -> case coe v1 of
             C_K_8 v2
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Id_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C__'8853'__12 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C__'8855'__14 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'8853'__12 v2 v3
        -> case coe v1 of
             C_K_8 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Id_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C__'8853'__12 v4 v5
               -> let v6 = d__'8799'IRFun__220 (coe v2) (coe v4) in
                  coe
                    (let v7 = d__'8799'IRFun__220 (coe v3) (coe v5) in
                     coe
                       (let v8
                              = case coe v7 of
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                    -> coe
                                         seq (coe v8)
                                         (coe
                                            seq (coe v9)
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                               (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                                  _ -> MAlonzo.RTE.mazUnreachableError in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                               -> let v11
                                        = case coe v7 of
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                              -> case coe v11 of
                                                   MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                     -> case coe v12 of
                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                            -> coe
                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                 (coe v11)
                                                                 (coe
                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                          _ -> coe v8
                                                   _ -> coe v8
                                            _ -> MAlonzo.RTE.mazUnreachableError in
                                  coe
                                    (if coe v9
                                       then case coe v10 of
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v12
                                                -> case coe v7 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                       -> case coe v13 of
                                                            MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                              -> case coe v14 of
                                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                                                                     -> coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                          (coe v13)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                             erased)
                                                                   _ -> coe v11
                                                            _ -> coe v11
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> coe v11
                                       else (case coe v10 of
                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                 -> coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v9)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                               _ -> coe v11))
                             _ -> MAlonzo.RTE.mazUnreachableError)))
             C__'8855'__14 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'8855'__14 v2 v3
        -> case coe v1 of
             C_K_8 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_Id_10
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C__'8853'__12 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C__'8855'__14 v4 v5
               -> let v6 = d__'8799'IRFun__220 (coe v2) (coe v4) in
                  coe
                    (let v7 = d__'8799'IRFun__220 (coe v3) (coe v5) in
                     coe
                       (let v8
                              = case coe v7 of
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                    -> coe
                                         seq (coe v8)
                                         (coe
                                            seq (coe v9)
                                            (coe
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                               (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                               (coe
                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                                  _ -> MAlonzo.RTE.mazUnreachableError in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                               -> let v11
                                        = case coe v7 of
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                              -> case coe v11 of
                                                   MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                     -> case coe v12 of
                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                            -> coe
                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                 (coe v11)
                                                                 (coe
                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                          _ -> coe v8
                                                   _ -> coe v8
                                            _ -> MAlonzo.RTE.mazUnreachableError in
                                  coe
                                    (if coe v9
                                       then case coe v10 of
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v12
                                                -> case coe v7 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                       -> case coe v13 of
                                                            MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                              -> case coe v14 of
                                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v15
                                                                     -> coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                          (coe v13)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                             erased)
                                                                   _ -> coe v11
                                                            _ -> coe v11
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> coe v11
                                       else (case coe v10 of
                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                 -> coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                      (coe v9)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                               _ -> coe v11))
                             _ -> MAlonzo.RTE.mazUnreachableError)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRTy.FitsInRegI
d_FitsInRegI_552 a0 = ()
data T_FitsInRegI_552 = C_fits'45'int_554 | C_fits'45'float_556
-- Once.IRTy.⟦_,_⟧-baseI
d_'10214'_'44'_'10215''45'baseI_558 :: () -> () -> T_IRTy_6 -> ()
d_'10214'_'44'_'10215''45'baseI_558 = erased
-- Once.IRTy.⌈_⌉
d_'8968'_'8969'_604 ::
  T_IRTy_6 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_'8968'_'8969'_604 v0
  = case coe v0 of
      C_Unit_16 -> coe MAlonzo.Code.Once.Spec.Type.C_Unit_18
      C_Void_18 -> coe MAlonzo.Code.Once.Spec.Type.C_Void_20
      C__'42'__20 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'42'__22
             (coe d_'8968'_'8969'_604 (coe v1))
             (coe d_'8968'_'8969'_604 (coe v2))
      C__'43'__22 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'43'__24
             (coe d_'8968'_'8969'_604 (coe v1))
             (coe d_'8968'_'8969'_604 (coe v2))
      C__'8667''91'_'93'__24 v1 v2 v3
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
             (coe d_'8968'_'8969'_604 (coe v1))
             (coe MAlonzo.Code.Once.Type.Grade.d_effK_32)
             (coe d_'8968'_'8969'_604 (coe v3))
      C_μ'45'type_26 v1
        -> coe
             MAlonzo.Code.Once.Spec.Type.C_μ_28
             (coe d_'8968'_'8969'F_606 (coe v1))
      C_ν'45'type_28 v1
        -> coe
             MAlonzo.Code.Once.Spec.Type.C_ν_30
             (coe d_'8968'_'8969'F_606 (coe v1))
             (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38)
      C_Int_30 -> coe MAlonzo.Code.Once.Spec.Type.C_Int_32
      C_Float_32 -> coe MAlonzo.Code.Once.Spec.Type.C_Float_34
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRTy.⌈_⌉F
d_'8968'_'8969'F_606 ::
  T_IRFunctor_4 -> MAlonzo.Code.Once.Spec.Type.T_Fun_12
d_'8968'_'8969'F_606 v0
  = case coe v0 of
      C_K_8 v1
        -> coe
             MAlonzo.Code.Once.Spec.Type.C_K_38
             (coe d_'8968'_'8969'_604 (coe v1))
      C_Id_10 -> coe MAlonzo.Code.Once.Spec.Type.C_Id_40
      C__'8853'__12 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'8853'__42
             (coe d_'8968'_'8969'F_606 (coe v1))
             (coe d_'8968'_'8969'F_606 (coe v2))
      C__'8855'__14 v1 v2
        -> coe
             MAlonzo.Code.Once.Spec.Type.C__'8855'__44
             (coe d_'8968'_'8969'F_606 (coe v1))
             (coe d_'8968'_'8969'F_606 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRTy.⌈⟧TI-commute
d_'8968''10215'TI'45'commute_638 ::
  T_IRFunctor_4 ->
  T_IRTy_6 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8968''10215'TI'45'commute_638 = erased
-- Once.IRTy.⌊⟧T-commute
d_'8970''10215'T'45'commute_664 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8970''10215'T'45'commute_664 = erased
-- Once.IRTy.⌊wk₀⌋
d_'8970'wk'8320''8971'_688 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8970'wk'8320''8971'_688 = erased
-- Once.IRTy.eraseF-wk₀
d_eraseF'45'wk'8320'_694 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Fun_12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eraseF'45'wk'8320'_694 = erased
