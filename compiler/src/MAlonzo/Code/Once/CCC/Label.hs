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

module MAlonzo.Code.Once.CCC.Label where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Properties
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Target.Symbol
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.CCC.Label.LabelId
d_LabelId_6 = ()
data T_LabelId_6
  = C_mkLabelId_20 MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
                   [Integer] Integer
-- Once.CCC.Label.LabelId.owner
d_owner_14 ::
  T_LabelId_6 -> MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4
d_owner_14 v0
  = case coe v0 of
      C_mkLabelId_20 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Label.LabelId.path
d_path_16 :: T_LabelId_6 -> [Integer]
d_path_16 v0
  = case coe v0 of
      C_mkLabelId_20 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Label.LabelId.idx
d_idx_18 :: T_LabelId_6 -> Integer
d_idx_18 v0
  = case coe v0 of
      C_mkLabelId_20 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Label.Label
d_Label_22 = ()
data T_Label_22
  = C_once_24 T_LabelId_6 |
    C_sigop_26 MAlonzo.Code.Agda.Builtin.String.T_String_6 Integer |
    C_thunk_28 T_LabelId_6
-- Once.CCC.Label._≟ᴵ_
d__'8799''7477'__30 ::
  T_LabelId_6 ->
  T_LabelId_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799''7477'__30 v0 v1
  = case coe v0 of
      C_mkLabelId_20 v2 v3 v4
        -> case coe v1 of
             C_mkLabelId_20 v5 v6 v7
               -> let v8
                        = coe
                            MAlonzo.Code.Data.List.Properties.du_'8801''45'dec_60
                            (coe MAlonzo.Code.Data.String.Properties.d__'8799'__54)
                            (coe MAlonzo.Code.Once.CanonicalName.d_parts_8 (coe v2))
                            (coe MAlonzo.Code.Once.CanonicalName.d_parts_8 (coe v5)) in
                  coe
                    (case coe v8 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                         -> if coe v9
                              then let v11
                                         = seq
                                             (coe v10)
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                (coe v9)
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                   erased)) in
                                   coe
                                     (case coe v11 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                          -> if coe v12
                                               then coe
                                                      seq (coe v13)
                                                      (let v14
                                                             = coe
                                                                 MAlonzo.Code.Data.List.Properties.du_'8801''45'dec_60
                                                                 (coe
                                                                    MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796)
                                                                 (coe v3) (coe v6) in
                                                       coe
                                                         (case coe v14 of
                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                                              -> if coe v15
                                                                   then coe
                                                                          seq (coe v16)
                                                                          (let v17
                                                                                 = coe
                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                     erased
                                                                                     (\ v17 ->
                                                                                        coe
                                                                                          MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                                                                          (coe v4))
                                                                                     (coe
                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                                                                                        (coe
                                                                                           eqInt
                                                                                           (coe v4)
                                                                                           (coe
                                                                                              v7))) in
                                                                           coe
                                                                             (case coe v17 of
                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                  -> if coe v18
                                                                                       then coe
                                                                                              seq
                                                                                              (coe
                                                                                                 v19)
                                                                                              (coe
                                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                 (coe
                                                                                                    v18)
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                    erased))
                                                                                       else coe
                                                                                              seq
                                                                                              (coe
                                                                                                 v19)
                                                                                              (coe
                                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                 (coe
                                                                                                    v18)
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                                                   else coe
                                                                          seq (coe v16)
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                             (coe v15)
                                                                             (coe
                                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                            _ -> MAlonzo.RTE.mazUnreachableError))
                                               else coe
                                                      seq (coe v13)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                         (coe v12)
                                                         (coe
                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              else (let v11
                                          = seq
                                              (coe v10)
                                              (coe
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                 (coe v9)
                                                 (coe
                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                    coe
                                      (case coe v11 of
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                           -> if coe v12
                                                then coe
                                                       seq (coe v13)
                                                       (let v14
                                                              = coe
                                                                  MAlonzo.Code.Data.List.Properties.du_'8801''45'dec_60
                                                                  (coe
                                                                     MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796)
                                                                  (coe v3) (coe v6) in
                                                        coe
                                                          (case coe v14 of
                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                                               -> if coe v15
                                                                    then coe
                                                                           seq (coe v16)
                                                                           (let v17
                                                                                  = coe
                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                      erased
                                                                                      (\ v17 ->
                                                                                         coe
                                                                                           MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2786
                                                                                           (coe v4))
                                                                                      (coe
                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                                                                                         (coe
                                                                                            eqInt
                                                                                            (coe v4)
                                                                                            (coe
                                                                                               v7))) in
                                                                            coe
                                                                              (case coe v17 of
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                   -> if coe v18
                                                                                        then coe
                                                                                               seq
                                                                                               (coe
                                                                                                  v19)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                  (coe
                                                                                                     v18)
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                                                     erased))
                                                                                        else coe
                                                                                               seq
                                                                                               (coe
                                                                                                  v19)
                                                                                               (coe
                                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                                                  (coe
                                                                                                     v18)
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                                                                    else coe
                                                                           seq (coe v16)
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                              (coe v15)
                                                                              (coe
                                                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                             _ -> MAlonzo.RTE.mazUnreachableError))
                                                else coe
                                                       seq (coe v13)
                                                       (coe
                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                          (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                         _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Label._≡ᵇᴵ_
d__'8801''7495''7477'__140 :: T_LabelId_6 -> T_LabelId_6 -> Bool
d__'8801''7495''7477'__140 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_'8970'_'8971'_140 ()
      erased (d__'8799''7477'__30 (coe v0) (coe v1))
-- Once.CCC.Label.≡ᵇᴵ-true
d_'8801''7495''7477''45'true_150 ::
  T_LabelId_6 ->
  T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''7477''45'true_150 = erased
-- Once.CCC.Label._.subst-T
d_subst'45'T_162 ::
  T_LabelId_6 ->
  T_LabelId_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_subst'45'T_162 ~v0 ~v1 ~v2 ~v3 = du_subst'45'T_162
du_subst'45'T_162 :: AgdaAny
du_subst'45'T_162 = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
-- Once.CCC.Label.≡ᵇᴵ-refl
d_'8801''7495''7477''45'refl_172 ::
  T_LabelId_6 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''7477''45'refl_172 = erased
-- Once.CCC.Label.≢⇒≡ᵇᴵfalse
d_'8802''8658''8801''7495''7477'false_194 ::
  T_LabelId_6 ->
  T_LabelId_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8802''8658''8801''7495''7477'false_194 = erased
-- Once.CCC.Label._≡ᵇᴸ_
d__'8801''7495''7480'__224 :: T_Label_22 -> T_Label_22 -> Bool
d__'8801''7495''7480'__224 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         C_once_24 v3
           -> case coe v1 of
                C_once_24 v4 -> coe d__'8801''7495''7477'__140 (coe v3) (coe v4)
                _ -> coe v2
         C_sigop_26 v3 v4
           -> case coe v1 of
                C_sigop_26 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe
                          MAlonzo.Code.Data.String.Properties.d__'61''61'__86 (coe v3)
                          (coe v5))
                       (coe eqInt (coe v4) (coe v6))
                _ -> coe v2
         C_thunk_28 v3
           -> case coe v1 of
                C_thunk_28 v4 -> coe d__'8801''7495''7477'__140 (coe v3) (coe v4)
                _ -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CCC.Label.showPath
d_showPath_242 ::
  [Integer] -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPath_242 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("_" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
                (d_showPath_242 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CCC.Label.showLabelId
d_showLabelId_248 ::
  T_LabelId_6 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showLabelId_248 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      (MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'path_52
         (coe d_owner_14 (coe v0)))
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (d_showPath_242 (coe d_path_16 (coe v0)))
         (coe
            MAlonzo.Code.Data.String.Base.d__'43''43'__20
            ("_" :: Data.Text.Text)
            (coe MAlonzo.Code.Data.Nat.Show.d_show_56 (d_idx_18 (coe v0)))))
-- Once.CCC.Label.ℓ
d_ℓ_252 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  Integer -> T_LabelId_6
d_ℓ_252 v0 v1
  = coe
      C_mkLabelId_20 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v1)
