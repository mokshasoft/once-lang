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

module MAlonzo.Code.Once.Target.SymbolValid where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.All.Properties
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Once.CCC.Label
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Target.AsmSymbol
import qualified MAlonzo.Code.Once.Target.Symbol
import qualified MAlonzo.Code.Once.Target.SymbolInjective
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Target.SymbolValid.SymCont
d_SymCont_6 :: [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> ()
d_SymCont_6 = erased
-- Once.Target.SymbolValid.∨-true
d_'8744''45'true_12 :: Bool -> AgdaAny
d_'8744''45'true_12 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.Target.SymbolValid.bool-lem
d_bool'45'lem_22 ::
  Bool ->
  Bool ->
  Bool ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_bool'45'lem_22 v0 v1 v2 v3 ~v4 = du_bool'45'lem_22 v0 v1 v2 v3
du_bool'45'lem_22 :: Bool -> Bool -> Bool -> Bool -> AgdaAny
du_bool'45'lem_22 v0 v1 v2 v3
  = if coe v0
      then coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      else (if coe v1
              then coe
                     d_'8744''45'true_12
                     (coe MAlonzo.Code.Data.Bool.Base.d__'8744'__30 (coe v2) (coe v3))
              else coe seq (coe v2) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Once.Target.SymbolValid.digit-cont
d_digit'45'cont_40 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_digit'45'cont_40 v0 ~v1 = du_digit'45'cont_40 v0
du_digit'45'cont_40 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> AgdaAny
du_digit'45'cont_40 v0
  = coe
      d_'8744''45'true_12
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8744'__30
         (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsAlpha_12 v0)
         (coe MAlonzo.Code.Once.Target.AsmSymbol.d_sym'45'punct_6 (coe v0)))
-- Once.Target.SymbolValid.digits-cont
d_digits'45'cont_50 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_digits'45'cont_50 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164
      (\ v1 v2 -> coe du_digit'45'cont_40 v1)
      (coe
         MAlonzo.Code.Data.Nat.Show.du_charsInBase_64 (coe (10 :: Integer))
         (coe v0))
      (coe
         MAlonzo.Code.Once.Target.SymbolInjective.d_charsInBase'45'all'45'digits_164
         (coe v0))
-- Once.Target.SymbolValid.showNat-cont
d_showNat'45'cont_58 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_showNat'45'cont_58 v0 = coe d_digits'45'cont_50 (coe v0)
-- Once.Target.SymbolValid.zchar-cont-aux
d_zchar'45'cont'45'aux_80 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_zchar'45'cont'45'aux_80 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9
  = du_zchar'45'cont'45'aux_80 v0 v1 v2 v3 v4 v5 v6 v7 v8
du_zchar'45'cont'45'aux_80 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Bool -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_zchar'45'cont'45'aux_80 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v1 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
        -> if coe v9
             then coe
                    seq (coe v10)
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                       (coe
                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                          (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
             else coe
                    seq (coe v10)
                    (case coe v2 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                         -> if coe v11
                              then coe
                                     seq (coe v12)
                                     (coe
                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                        (coe
                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                           (coe
                                              MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                              else coe
                                     seq (coe v12)
                                     (case coe v3 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                          -> if coe v13
                                               then coe
                                                      seq (coe v14)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                            (coe
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                                               else coe
                                                      seq (coe v14)
                                                      (case coe v4 of
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                                           -> if coe v15
                                                                then coe
                                                                       seq (coe v16)
                                                                       (coe
                                                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                          (coe
                                                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                             (coe
                                                                                MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                                                                else coe
                                                                       seq (coe v16)
                                                                       (case coe v5 of
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                            -> if coe v17
                                                                                 then coe
                                                                                        seq
                                                                                        (coe v18)
                                                                                        (coe
                                                                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                           (coe
                                                                                              MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                           (coe
                                                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                              (coe
                                                                                                 MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                              (coe
                                                                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                                                                                 else coe
                                                                                        seq
                                                                                        (coe v18)
                                                                                        (case coe
                                                                                                v6 of
                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v19 v20
                                                                                             -> if coe
                                                                                                     v19
                                                                                                  then coe
                                                                                                         seq
                                                                                                         (coe
                                                                                                            v20)
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                                                                                                  else coe
                                                                                                         seq
                                                                                                         (coe
                                                                                                            v20)
                                                                                                         (case coe
                                                                                                                 v7 of
                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                                                                              -> if coe
                                                                                                                      v21
                                                                                                                   then coe
                                                                                                                          seq
                                                                                                                          (coe
                                                                                                                             v22)
                                                                                                                          (coe
                                                                                                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                                (coe
                                                                                                                                   MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                                (coe
                                                                                                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))
                                                                                                                   else coe
                                                                                                                          seq
                                                                                                                          (coe
                                                                                                                             v22)
                                                                                                                          (if coe
                                                                                                                                v8
                                                                                                                             then coe
                                                                                                                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                                    (coe
                                                                                                                                       du_bool'45'lem_22
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Agda.Builtin.Char.d_primIsAlpha_12
                                                                                                                                          v0)
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Agda.Builtin.Char.d_primIsDigit_10
                                                                                                                                          v0)
                                                                                                                                       (coe
                                                                                                                                          eqInt
                                                                                                                                          (coe
                                                                                                                                             MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28
                                                                                                                                             v0)
                                                                                                                                          (coe
                                                                                                                                             MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28
                                                                                                                                             '_'))
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                                                                                                                                          (coe
                                                                                                                                             eqInt
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28
                                                                                                                                                v0)
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28
                                                                                                                                                '.'))
                                                                                                                                          (coe
                                                                                                                                             eqInt
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28
                                                                                                                                                v0)
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28
                                                                                                                                                '$'))))
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
                                                                                                                             else coe
                                                                                                                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                                                                                                                                          (coe
                                                                                                                                             MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Once.Target.Symbol.d_showNat_6
                                                                                                                                                (coe
                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28
                                                                                                                                                   v0)))
                                                                                                                                          (coe
                                                                                                                                             d_showNat'45'cont_58
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28
                                                                                                                                                v0))
                                                                                                                                          (coe
                                                                                                                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)))))
                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.SymbolValid.zchar-cont
d_zchar'45'cont_104 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_zchar'45'cont_104 v0
  = coe
      du_zchar'45'cont'45'aux_80 (coe v0)
      (coe
         MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0) (coe 'z'))
      (coe
         MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0)
         (coe '\''))
      (coe
         MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0) (coe '+'))
      (coe
         MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0) (coe '*'))
      (coe
         MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0) (coe '!'))
      (coe
         MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0) (coe '?'))
      (coe
         MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0) (coe '.'))
      (coe
         MAlonzo.Code.Once.Target.Symbol.d_symbol'45'char'63'_10 (coe v0))
-- Once.Target.SymbolValid.zencL-cont
d_zencL'45'cont_110 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_zencL'45'cont_110 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
             (coe
                MAlonzo.Code.Once.Target.Symbol.d_z'45'encode'45'char_36 (coe v1))
             (coe d_zchar'45'cont_104 (coe v1))
             (coe d_zencL'45'cont_110 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.SymbolValid.mangL-cont
d_mangL'45'cont_118 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_mangL'45'cont_118 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe
         MAlonzo.Code.Data.Nat.Show.du_charsInBase_64 (coe (10 :: Integer))
         (coe
            MAlonzo.Code.Data.List.Base.du_length_268
            (coe MAlonzo.Code.Once.Target.SymbolInjective.d_zencL_142 v0)))
      (coe
         d_digits'45'cont_50
         (coe
            MAlonzo.Code.Data.List.Base.du_length_268
            (coe MAlonzo.Code.Once.Target.SymbolInjective.d_zencL_142 v0)))
      (coe d_zencL'45'cont_110 (coe v0))
-- Once.Target.SymbolValid.withSep-cont
d_withSep'45'cont_124 ::
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_withSep'45'cont_124 v0 v1
  = case coe v0 of
      []
        -> coe
             seq (coe v1)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6 v7
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                       (coe v2) (coe v6) (coe d_withSep'45'cont_124 (coe v3) (coe v7)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.SymbolValid.joinUs-cont
d_joinUs'45'cont_136 ::
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_joinUs'45'cont_136 v0 v1
  = case coe v0 of
      []
        -> coe
             seq (coe v1)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6 v7
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                    (coe v2) (coe v6) (coe d_withSep'45'cont_124 (coe v3) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.SymbolValid.mangs-cont
d_mangs'45'cont_148 ::
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_mangs'45'cont_148 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
             (d_mangL'45'cont_118 (coe v1)) (d_mangs'45'cont_148 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.SymbolValid.asm-chars-++
d_asm'45'chars'45''43''43'_158 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_asm'45'chars'45''43''43'_158 v0 ~v1 v2 v3
  = du_asm'45'chars'45''43''43'_158 v0 v2 v3
du_asm'45'chars'45''43''43'_158 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_asm'45'chars'45''43''43'_158 v0 v1 v2
  = case coe v0 of
      (:) v3 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
                       (coe v4) (coe v6) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.SymbolValid.asm-++
d_asm'45''43''43'_180 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
d_asm'45''43''43'_180 v0 ~v1 v2 v3
  = du_asm'45''43''43'_180 v0 v2 v3
du_asm'45''43''43'_180 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 -> AgdaAny
du_asm'45''43''43'_180 v0 v1 v2
  = coe
      du_asm'45'chars'45''43''43'_158
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
      (coe v1) (coe v2)
-- Once.Target.SymbolValid.start⇒cont
d_start'8658'cont_192 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> AgdaAny -> AgdaAny
d_start'8658'cont_192 v0 ~v1 = du_start'8658'cont_192 v0
du_start'8658'cont_192 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> AgdaAny
du_start'8658'cont_192 v0
  = let v1
          = MAlonzo.Code.Data.Bool.Base.d__'8744'__30
              (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsAlpha_12 v0)
              (coe
                 MAlonzo.Code.Once.Target.AsmSymbol.d_sym'45'punct_6 (coe v0)) in
    coe (coe seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Once.Target.SymbolValid.asm-chars-cont
d_asm'45'chars'45'cont_208 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_asm'45'chars'45'cont_208 v0 v1
  = case coe v0 of
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                    (coe du_start'8658'cont_192 (coe v2)) v5
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.SymbolValid.cont-++
d_cont'45''43''43'_222 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_cont'45''43''43'_222 v0 ~v1 v2 v3
  = du_cont'45''43''43'_222 v0 v2 v3
du_cont'45''43''43'_222 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_cont'45''43''43'_222 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.Properties.du_'43''43''8314'_580
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
      (coe v1) (coe v2)
-- Once.Target.SymbolValid.once-symbol-path-asm
d_once'45'symbol'45'path'45'asm_234 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> AgdaAny
d_once'45'symbol'45'path'45'asm_234 v0
  = coe
      du_asm'45''43''43'_180
      (coe MAlonzo.Code.Once.Target.Symbol.d_once'45'prefix_8)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                     (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))
      (coe
         d_joinUs'45'cont_136
         (coe
            MAlonzo.Code.Data.List.Base.du_map_22
            (coe MAlonzo.Code.Once.Target.SymbolInjective.d_mangL_646)
            (coe
               MAlonzo.Code.Data.List.Base.du_map_22
               (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12)
               (coe MAlonzo.Code.Once.CanonicalName.d_parts_8 (coe v0))))
         (coe
            d_mangs'45'cont_148
            (coe
               MAlonzo.Code.Data.List.Base.du_map_22
               (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12)
               (coe MAlonzo.Code.Once.CanonicalName.d_parts_8 (coe v0)))))
-- Once.Target.SymbolValid.once-symbol-own-asm
d_once'45'symbol'45'own'45'asm_240 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
d_once'45'symbol'45'own'45'asm_240 v0
  = coe
      d_once'45'symbol'45'path'45'asm_234
      (coe
         MAlonzo.Code.Once.CanonicalName.C_canonical_10
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- Once.Target.SymbolValid.showPath-cont
d_showPath'45'cont_246 ::
  [Integer] -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_showPath'45'cont_246 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v1 v2
        -> coe
             du_cont'45''43''43'_222 (coe ("_" :: Data.Text.Text))
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             (coe
                du_cont'45''43''43'_222
                (coe MAlonzo.Code.Once.Target.Symbol.d_showNat_6 v1)
                (coe d_showNat'45'cont_58 (coe v1))
                (coe d_showPath'45'cont_246 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.SymbolValid.showLabelId-cont
d_showLabelId'45'cont_254 ::
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_showLabelId'45'cont_254 v0
  = coe
      du_cont'45''43''43'_222
      (coe
         MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'path_58
         (coe MAlonzo.Code.Once.CCC.Label.d_owner_14 (coe v0)))
      (coe
         d_asm'45'chars'45'cont_208
         (coe
            MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
            (MAlonzo.Code.Once.Target.Symbol.d_once'45'symbol'45'path_58
               (coe MAlonzo.Code.Once.CCC.Label.d_owner_14 (coe v0))))
         (coe
            d_once'45'symbol'45'path'45'asm_234
            (coe MAlonzo.Code.Once.CCC.Label.d_owner_14 (coe v0))))
      (coe
         du_cont'45''43''43'_222
         (coe
            MAlonzo.Code.Once.CCC.Label.d_showPath_378
            (coe MAlonzo.Code.Once.CCC.Label.d_path_16 (coe v0)))
         (coe
            d_showPath'45'cont_246
            (coe MAlonzo.Code.Once.CCC.Label.d_path_16 (coe v0)))
         (coe
            du_cont'45''43''43'_222 (coe ("_" :: Data.Text.Text))
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
               (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
            (coe
               d_showNat'45'cont_58
               (coe MAlonzo.Code.Once.CCC.Label.d_idx_18 (coe v0)))))
-- Once.Target.SymbolValid.thunkSym-asm
d_thunkSym'45'asm_260 ::
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> AgdaAny
d_thunkSym'45'asm_260 v0
  = coe
      du_asm'45''43''43'_180 (coe (".L_thunk_" :: Data.Text.Text))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
      (coe d_showLabelId'45'cont_254 (coe v0))
-- Once.Target.SymbolValid.entrySym-asm
d_entrySym'45'asm_266 ::
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 -> AgdaAny
d_entrySym'45'asm_266 v0
  = case coe v0 of
      MAlonzo.Code.Once.CCC.Label.C_e'45'thunk_24 v1
        -> coe d_thunkSym'45'asm_260 (coe v1)
      MAlonzo.Code.Once.CCC.Label.C_e'45'fn_26 v1
        -> coe d_once'45'symbol'45'path'45'asm_234 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.SymbolValid.once-label-asm
d_once'45'label'45'asm_274 ::
  MAlonzo.Code.Once.CCC.Label.T_LabelId_6 -> AgdaAny
d_once'45'label'45'asm_274 v0
  = coe
      du_asm'45''43''43'_180 (coe (".Lonce_" :: Data.Text.Text))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))
      (coe d_showLabelId'45'cont_254 (coe v0))
-- Once.Target.SymbolValid.callee-label-asm
d_callee'45'label'45'asm_280 ::
  MAlonzo.Code.Once.CCC.Label.T_EntryId_22 -> AgdaAny
d_callee'45'label'45'asm_280 = coe d_entrySym'45'asm_266
