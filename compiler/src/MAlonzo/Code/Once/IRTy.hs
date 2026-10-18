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
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
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
    C__'43'__22 T_IRTy_6 T_IRTy_6 | C__'8667'__24 T_IRTy_6 T_IRTy_6 |
    C_μ'45'type_26 T_IRFunctor_4 | C_ν'45'type_28 T_IRFunctor_4 |
    C_Int_30 | C_Float_32
-- Once.IRTy.eraseArrow
d_eraseArrow_34 ::
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  T_IRTy_6 -> T_IRTy_6 -> T_IRTy_6
d_eraseArrow_34 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
        -> coe C__'8667'__24 (coe C_Unit_16) (coe v2)
      MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
        -> coe C__'8667'__24 (coe v1) (coe v2)
      MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
        -> coe C__'8667'__24 (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRTy.⌊_⌋
d_'8970'_'8971'_48 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 -> T_IRTy_6
d_'8970'_'8971'_48 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_Unit_20 -> coe C_Unit_16
      MAlonzo.Code.Once.Lang.Type.C_Void_22 -> coe C_Void_18
      MAlonzo.Code.Once.Lang.Type.C__'42'__24 v1 v2
        -> coe
             C__'42'__20 (coe d_'8970'_'8971'_48 (coe v1))
             (coe d_'8970'_'8971'_48 (coe v2))
      MAlonzo.Code.Once.Lang.Type.C__'43'__26 v1 v2
        -> coe
             C__'43'__22 (coe d_'8970'_'8971'_48 (coe v1))
             (coe d_'8970'_'8971'_48 (coe v2))
      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v1 v2 v3
        -> coe
             d_eraseArrow_34
             (coe MAlonzo.Code.Once.Lang.Type.Grade.d_quantity_74 (coe v2))
             (coe d_'8970'_'8971'_48 (coe v1)) (coe d_'8970'_'8971'_48 (coe v3))
      MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v1
        -> coe C_μ'45'type_26 (coe d_eraseF_50 (coe v1))
      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v1 v2
        -> coe C_ν'45'type_28 (coe d_eraseF_50 (coe v1))
      MAlonzo.Code.Once.Lang.Type.C_Int_34 -> coe C_Int_30
      MAlonzo.Code.Once.Lang.Type.C_Float_36 -> coe C_Float_32
      MAlonzo.Code.Once.Lang.Type.C_rigid_38 v1 v2 -> coe C_Void_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRTy.eraseF
d_eraseF_50 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 -> T_IRFunctor_4
d_eraseF_50 v0
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Type.C_K_12 v1
        -> coe C_K_8 (coe d_'8970'_'8971'_48 (coe v1))
      MAlonzo.Code.Once.Lang.Type.C_Id_14 -> coe C_Id_10
      MAlonzo.Code.Once.Lang.Type.C__'8853'__16 v1 v2
        -> coe
             C__'8853'__12 (coe d_eraseF_50 (coe v1)) (coe d_eraseF_50 (coe v2))
      MAlonzo.Code.Once.Lang.Type.C__'8855'__18 v1 v2
        -> coe
             C__'8855'__14 (coe d_eraseF_50 (coe v1)) (coe d_eraseF_50 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRTy.⟦_⟧TI
d_'10214'_'10215'TI_80 :: T_IRFunctor_4 -> T_IRTy_6 -> T_IRTy_6
d_'10214'_'10215'TI_80 v0 v1
  = case coe v0 of
      C_K_8 v2 -> coe v2
      C_Id_10 -> coe v1
      C__'8853'__12 v2 v3
        -> coe
             C__'43'__22 (coe d_'10214'_'10215'TI_80 (coe v2) (coe v1))
             (coe d_'10214'_'10215'TI_80 (coe v3) (coe v1))
      C__'8855'__14 v2 v3
        -> coe
             C__'42'__20 (coe d_'10214'_'10215'TI_80 (coe v2) (coe v1))
             (coe d_'10214'_'10215'TI_80 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRTy.IsBaseTypeI
d_IsBaseTypeI_100 a0 = ()
data T_IsBaseTypeI_100
  = C_base'45'Unit_102 | C_base'45'Void_104 | C_base'45'Int_106 |
    C_base'45'Float_108 |
    C_base'45'Prod_114 T_IsBaseTypeI_100 T_IsBaseTypeI_100 |
    C_base'45'Sum_120 T_IsBaseTypeI_100 T_IsBaseTypeI_100
-- Once.IRTy.WellFormedFI
d_WellFormedFI_122 a0 = ()
data T_WellFormedFI_122
  = C_wf'45'K_126 T_IsBaseTypeI_100 | C_wf'45'Id_128 |
    C_wf'45'Sum_134 T_WellFormedFI_122 T_WellFormedFI_122 |
    C_wf'45'Prod_140 T_WellFormedFI_122 T_WellFormedFI_122
-- Once.IRTy.IsBaseTypeI-irrelevant
d_IsBaseTypeI'45'irrelevant_148 ::
  T_IRTy_6 ->
  T_IsBaseTypeI_100 ->
  T_IsBaseTypeI_100 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_IsBaseTypeI'45'irrelevant_148 = erased
-- Once.IRTy.WellFormedFI-irrelevant
d_WellFormedFI'45'irrelevant_172 ::
  T_IRFunctor_4 ->
  T_WellFormedFI_122 ->
  T_WellFormedFI_122 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_WellFormedFI'45'irrelevant_172 = erased
-- Once.IRTy.irtyTag
d_irtyTag_194 :: T_IRTy_6 -> Integer
d_irtyTag_194 v0
  = case coe v0 of
      C_Unit_16 -> coe (0 :: Integer)
      C_Void_18 -> coe (1 :: Integer)
      C__'42'__20 v1 v2 -> coe (2 :: Integer)
      C__'43'__22 v1 v2 -> coe (3 :: Integer)
      C__'8667'__24 v1 v2 -> coe (4 :: Integer)
      C_μ'45'type_26 v1 -> coe (5 :: Integer)
      C_ν'45'type_28 v1 -> coe (6 :: Integer)
      C_Int_30 -> coe (7 :: Integer)
      C_Float_32 -> coe (8 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRTy._≟IRTy_
d__'8799'IRTy__196 ::
  T_IRTy_6 ->
  T_IRTy_6 -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'IRTy__196 v0 v1
  = coe
      d_'8799'IRTy'45'aux_202 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796
         (coe d_irtyTag_194 (coe v0)) (coe d_irtyTag_194 (coe v1)))
-- Once.IRTy.≟IRTy-aux
d_'8799'IRTy'45'aux_202 ::
  T_IRTy_6 ->
  T_IRTy_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRTy'45'aux_202 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe
                    seq (coe v4) (coe du_'8799'IRTy'45'diag_208 (coe v0) (coe v1))
             else coe
                    seq (coe v4)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe v3)
                       (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRTy.≟IRTy-diag
d_'8799'IRTy'45'diag_208 ::
  T_IRTy_6 ->
  T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8799'IRTy'45'diag_208 v0 v1 ~v2
  = du_'8799'IRTy'45'diag_208 v0 v1
du_'8799'IRTy'45'diag_208 ::
  T_IRTy_6 ->
  T_IRTy_6 -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8799'IRTy'45'diag_208 v0 v1
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
                        = d_'8799'IRTy'45'aux_202
                            (coe v2) (coe v4)
                            (coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v6 ->
                                  coe
                                    MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                    (coe d_irtyTag_194 (coe v2)))
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                  (coe
                                     eqInt (coe d_irtyTag_194 (coe v2))
                                     (coe d_irtyTag_194 (coe v4)))
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                     (coe
                                        eqInt (coe d_irtyTag_194 (coe v2))
                                        (coe d_irtyTag_194 (coe v4)))))) in
                  coe
                    (let v7
                           = d_'8799'IRTy'45'aux_202
                               (coe v3) (coe v5)
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                  erased
                                  (\ v7 ->
                                     coe
                                       MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                       (coe d_irtyTag_194 (coe v3)))
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                     (coe
                                        eqInt (coe d_irtyTag_194 (coe v3))
                                        (coe d_irtyTag_194 (coe v5)))
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                        (coe
                                           eqInt (coe d_irtyTag_194 (coe v3))
                                           (coe d_irtyTag_194 (coe v5)))))) in
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
                        = d_'8799'IRTy'45'aux_202
                            (coe v2) (coe v4)
                            (coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v6 ->
                                  coe
                                    MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                    (coe d_irtyTag_194 (coe v2)))
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                  (coe
                                     eqInt (coe d_irtyTag_194 (coe v2))
                                     (coe d_irtyTag_194 (coe v4)))
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                     (coe
                                        eqInt (coe d_irtyTag_194 (coe v2))
                                        (coe d_irtyTag_194 (coe v4)))))) in
                  coe
                    (let v7
                           = d_'8799'IRTy'45'aux_202
                               (coe v3) (coe v5)
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                  erased
                                  (\ v7 ->
                                     coe
                                       MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                       (coe d_irtyTag_194 (coe v3)))
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                     (coe
                                        eqInt (coe d_irtyTag_194 (coe v3))
                                        (coe d_irtyTag_194 (coe v5)))
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                        (coe
                                           eqInt (coe d_irtyTag_194 (coe v3))
                                           (coe d_irtyTag_194 (coe v5)))))) in
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
      C__'8667'__24 v2 v3
        -> case coe v1 of
             C__'8667'__24 v4 v5
               -> let v6
                        = d_'8799'IRTy'45'aux_202
                            (coe v2) (coe v4)
                            (coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v6 ->
                                  coe
                                    MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                    (coe d_irtyTag_194 (coe v2)))
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                  (coe
                                     eqInt (coe d_irtyTag_194 (coe v2))
                                     (coe d_irtyTag_194 (coe v4)))
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                     (coe
                                        eqInt (coe d_irtyTag_194 (coe v2))
                                        (coe d_irtyTag_194 (coe v4)))))) in
                  coe
                    (let v7
                           = d_'8799'IRTy'45'aux_202
                               (coe v3) (coe v5)
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                  erased
                                  (\ v7 ->
                                     coe
                                       MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                       (coe d_irtyTag_194 (coe v3)))
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                     (coe
                                        eqInt (coe d_irtyTag_194 (coe v3))
                                        (coe d_irtyTag_194 (coe v5)))
                                     (coe
                                        MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                        (coe
                                           eqInt (coe d_irtyTag_194 (coe v3))
                                           (coe d_irtyTag_194 (coe v5)))))) in
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
      C_μ'45'type_26 v2
        -> case coe v1 of
             C_μ'45'type_26 v3
               -> let v4 = d__'8799'IRFun__210 (coe v2) (coe v3) in
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
               -> let v4 = d__'8799'IRFun__210 (coe v2) (coe v3) in
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
d__'8799'IRFun__210 ::
  T_IRFunctor_4 ->
  T_IRFunctor_4 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'IRFun__210 v0 v1
  = case coe v0 of
      C_K_8 v2
        -> case coe v1 of
             C_K_8 v3
               -> let v4
                        = d_'8799'IRTy'45'aux_202
                            (coe v2) (coe v3)
                            (coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v4 ->
                                  coe
                                    MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                    (coe d_irtyTag_194 (coe v2)))
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                  (coe
                                     eqInt (coe d_irtyTag_194 (coe v2))
                                     (coe d_irtyTag_194 (coe v3)))
                                  (coe
                                     MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_70
                                     (coe
                                        eqInt (coe d_irtyTag_194 (coe v2))
                                        (coe d_irtyTag_194 (coe v3)))))) in
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
               -> let v6 = d__'8799'IRFun__210 (coe v2) (coe v4) in
                  coe
                    (let v7 = d__'8799'IRFun__210 (coe v3) (coe v5) in
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
               -> let v6 = d__'8799'IRFun__210 (coe v2) (coe v4) in
                  coe
                    (let v7 = d__'8799'IRFun__210 (coe v3) (coe v5) in
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
d_FitsInRegI_510 a0 = ()
data T_FitsInRegI_510 = C_fits'45'int_512 | C_fits'45'float_514
-- Once.IRTy.⟦_,_⟧-baseI
d_'10214'_'44'_'10215''45'baseI_516 :: () -> () -> T_IRTy_6 -> ()
d_'10214'_'44'_'10215''45'baseI_516 = erased
-- Once.IRTy.erase-⇒-purity-irrelevant
d_erase'45''8658''45'purity'45'irrelevant_572 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Quantity_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_erase'45''8658''45'purity'45'irrelevant_572 = erased
-- Once.IRTy.⌈_⌉
d_'8968'_'8969'_574 ::
  T_IRTy_6 -> MAlonzo.Code.Once.Lang.Type.T_Type_8
d_'8968'_'8969'_574 v0
  = case coe v0 of
      C_Unit_16 -> coe MAlonzo.Code.Once.Lang.Type.C_Unit_20
      C_Void_18 -> coe MAlonzo.Code.Once.Lang.Type.C_Void_22
      C__'42'__20 v1 v2
        -> coe
             MAlonzo.Code.Once.Lang.Type.C__'42'__24
             (coe d_'8968'_'8969'_574 (coe v1))
             (coe d_'8968'_'8969'_574 (coe v2))
      C__'43'__22 v1 v2
        -> coe
             MAlonzo.Code.Once.Lang.Type.C__'43'__26
             (coe d_'8968'_'8969'_574 (coe v1))
             (coe d_'8968'_'8969'_574 (coe v2))
      C__'8667'__24 v1 v2
        -> coe
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
             (coe d_'8968'_'8969'_574 (coe v1))
             (coe MAlonzo.Code.Once.Lang.Type.Grade.d_effK_84)
             (coe d_'8968'_'8969'_574 (coe v2))
      C_μ'45'type_26 v1
        -> coe
             MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30
             (coe d_'8968'_'8969'F_576 (coe v1))
      C_ν'45'type_28 v1
        -> coe
             MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32
             (coe d_'8968'_'8969'F_576 (coe v1))
             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_act_44)
      C_Int_30 -> coe MAlonzo.Code.Once.Lang.Type.C_Int_34
      C_Float_32 -> coe MAlonzo.Code.Once.Lang.Type.C_Float_36
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRTy.⌈_⌉F
d_'8968'_'8969'F_576 ::
  T_IRFunctor_4 -> MAlonzo.Code.Once.Lang.Type.T_Functor_6
d_'8968'_'8969'F_576 v0
  = case coe v0 of
      C_K_8 v1
        -> coe
             MAlonzo.Code.Once.Lang.Type.C_K_12
             (coe d_'8968'_'8969'_574 (coe v1))
      C_Id_10 -> coe MAlonzo.Code.Once.Lang.Type.C_Id_14
      C__'8853'__12 v1 v2
        -> coe
             MAlonzo.Code.Once.Lang.Type.C__'8853'__16
             (coe d_'8968'_'8969'F_576 (coe v1))
             (coe d_'8968'_'8969'F_576 (coe v2))
      C__'8855'__14 v1 v2
        -> coe
             MAlonzo.Code.Once.Lang.Type.C__'8855'__18
             (coe d_'8968'_'8969'F_576 (coe v1))
             (coe d_'8968'_'8969'F_576 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.IRTy.retract-⌈⌉
d_retract'45''8968''8969'_606 ::
  T_IRTy_6 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_retract'45''8968''8969'_606 = erased
-- Once.IRTy.retract-⌈⌉F
d_retract'45''8968''8969'F_610 ::
  T_IRFunctor_4 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_retract'45''8968''8969'F_610 = erased
-- Once.IRTy.⌈⟧TI-commute
d_'8968''10215'TI'45'commute_642 ::
  T_IRFunctor_4 ->
  T_IRTy_6 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8968''10215'TI'45'commute_642 = erased
-- Once.IRTy.⌊⟧T-commute
d_'8970''10215'T'45'commute_666 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8970''10215'T'45'commute_666 = erased
