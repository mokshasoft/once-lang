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

module MAlonzo.Code.Once.Target.SymbolInjective where

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
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.Digit
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.DivMod
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Target.Symbol
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Target.SymbolInjective.IsDigitC
d_IsDigitC_6 :: MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> ()
d_IsDigitC_6 = erased
-- Once.Target.SymbolInjective.NotDigitC
d_NotDigitC_10 :: MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> ()
d_NotDigitC_10 = erased
-- Once.Target.SymbolInjective.alpha⇒¬digit
d_alpha'8658''172'digit_16
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Target.SymbolInjective.alpha\8658\172digit"
-- Once.Target.SymbolInjective.showDigit10-isDigit
d_showDigit10'45'isDigit_20 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_showDigit10'45'isDigit_20 = erased
-- Once.Target.SymbolInjective.unescape-aux
d_unescape'45'aux_24 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6
d_unescape'45'aux_24 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v1 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
        -> if coe v8
             then coe seq (coe v9) (coe 'z')
             else coe
                    seq (coe v9)
                    (case coe v2 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                         -> if coe v10
                              then coe seq (coe v11) (coe '\'')
                              else coe
                                     seq (coe v11)
                                     (case coe v3 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                          -> if coe v12
                                               then coe seq (coe v13) (coe '+')
                                               else coe
                                                      seq (coe v13)
                                                      (case coe v4 of
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                           -> if coe v14
                                                                then coe seq (coe v15) (coe '*')
                                                                else coe
                                                                       seq (coe v15)
                                                                       (case coe v5 of
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                            -> if coe v16
                                                                                 then coe
                                                                                        seq
                                                                                        (coe v17)
                                                                                        (coe '!')
                                                                                 else coe
                                                                                        seq
                                                                                        (coe v17)
                                                                                        (case coe
                                                                                                v6 of
                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                             -> if coe
                                                                                                     v18
                                                                                                  then coe
                                                                                                         seq
                                                                                                         (coe
                                                                                                            v19)
                                                                                                         (coe
                                                                                                            '?')
                                                                                                  else coe
                                                                                                         seq
                                                                                                         (coe
                                                                                                            v19)
                                                                                                         (case coe
                                                                                                                 v7 of
                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                                                              -> if coe
                                                                                                                      v20
                                                                                                                   then coe
                                                                                                                          seq
                                                                                                                          (coe
                                                                                                                             v21)
                                                                                                                          (coe
                                                                                                                             '.')
                                                                                                                   else coe
                                                                                                                          seq
                                                                                                                          (coe
                                                                                                                             v21)
                                                                                                                          (coe
                                                                                                                             v0)
                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.SymbolInjective.unescape
d_unescape_42 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6
d_unescape_42 v0
  = coe
      d_unescape'45'aux_24 (coe v0)
      (coe
         MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0) (coe 'z'))
      (coe
         MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0) (coe 'q'))
      (coe
         MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0) (coe 'p'))
      (coe
         MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0) (coe 't'))
      (coe
         MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0) (coe 'b'))
      (coe
         MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0) (coe 'h'))
      (coe
         MAlonzo.Code.Data.Char.Properties.d__'8799'__14 (coe v0) (coe 'd'))
-- Once.Target.SymbolInjective.TagEsc
d_TagEsc_46 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> ()
d_TagEsc_46 = erased
-- Once.Target.SymbolInjective.GenEsc
d_GenEsc_54 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> ()
d_GenEsc_54 = erased
-- Once.Target.SymbolInjective.OrdChar
d_OrdChar_60 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> ()
d_OrdChar_60 = erased
-- Once.Target.SymbolInjective.ZClass
d_ZClass_66 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> ()
d_ZClass_66 = erased
-- Once.Target.SymbolInjective.toList-showNat′
d_toList'45'showNat'8242'_74 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toList'45'showNat'8242'_74 = erased
-- Once.Target.SymbolInjective.zec-class-aux
d_zec'45'class'45'aux_96 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_zec'45'class'45'aux_96 ~v0 v1 v2 v3 v4 v5 v6 v7 v8
  = du_zec'45'class'45'aux_96 v1 v2 v3 v4 v5 v6 v7 v8
du_zec'45'class'45'aux_96 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_zec'45'class'45'aux_96 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
        -> if coe v8
             then coe
                    seq (coe v9)
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe 'z')
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))))
             else coe
                    seq (coe v9)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                         -> if coe v10
                              then coe
                                     seq (coe v11)
                                     (coe
                                        MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe 'q')
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                                 erased))))
                              else coe
                                     seq (coe v11)
                                     (case coe v2 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                          -> if coe v12
                                               then coe
                                                      seq (coe v13)
                                                      (coe
                                                         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe 'p')
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               erased
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  erased erased))))
                                               else coe
                                                      seq (coe v13)
                                                      (case coe v3 of
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                           -> if coe v14
                                                                then coe
                                                                       seq (coe v15)
                                                                       (coe
                                                                          MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe 't')
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                erased
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                   erased erased))))
                                                                else coe
                                                                       seq (coe v15)
                                                                       (case coe v4 of
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                            -> if coe v16
                                                                                 then coe
                                                                                        seq
                                                                                        (coe v17)
                                                                                        (coe
                                                                                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                                                                           (coe
                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                              (coe
                                                                                                 'b')
                                                                                              (coe
                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                 erased
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                    erased
                                                                                                    erased))))
                                                                                 else coe
                                                                                        seq
                                                                                        (coe v17)
                                                                                        (case coe
                                                                                                v5 of
                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                             -> if coe
                                                                                                     v18
                                                                                                  then coe
                                                                                                         seq
                                                                                                         (coe
                                                                                                            v19)
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                               (coe
                                                                                                                  'h')
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                  erased
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                     erased
                                                                                                                     erased))))
                                                                                                  else coe
                                                                                                         seq
                                                                                                         (coe
                                                                                                            v19)
                                                                                                         (case coe
                                                                                                                 v6 of
                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v20 v21
                                                                                                              -> if coe
                                                                                                                      v20
                                                                                                                   then coe
                                                                                                                          seq
                                                                                                                          (coe
                                                                                                                             v21)
                                                                                                                          (coe
                                                                                                                             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                (coe
                                                                                                                                   'd')
                                                                                                                                (coe
                                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                   erased
                                                                                                                                   (coe
                                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                      erased
                                                                                                                                      erased))))
                                                                                                                   else coe
                                                                                                                          seq
                                                                                                                          (coe
                                                                                                                             v21)
                                                                                                                          (if coe
                                                                                                                                v7
                                                                                                                             then coe
                                                                                                                                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                          erased
                                                                                                                                          erased))
                                                                                                                             else coe
                                                                                                                                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                                                                                                                       erased))
                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.SymbolInjective.zec-class
d_zec'45'class_138 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_zec'45'class_138 v0
  = coe
      du_zec'45'class'45'aux_96
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
-- Once.Target.SymbolInjective.zencL
d_zencL_142 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_zencL_142
  = coe
      MAlonzo.Code.Data.List.Base.du_concatMap_246
      (coe MAlonzo.Code.Once.Target.Symbol.d_z'45'encode'45'char_36)
-- Once.Target.SymbolInjective.cons≢[]
d_cons'8802''91''93'_150 ::
  () ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_cons'8802''91''93'_150 = erased
-- Once.Target.SymbolInjective.false≢true
d_false'8802'true_152 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_false'8802'true_152 = erased
-- Once.Target.SymbolInjective.all-digits-mapped
d_all'45'digits'45'mapped_156 ::
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_all'45'digits'45'mapped_156 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
             (d_all'45'digits'45'mapped_156 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.SymbolInjective.charsInBase-all-digits
d_charsInBase'45'all'45'digits_164 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_charsInBase'45'all'45'digits_164 v0
  = coe
      d_all'45'digits'45'mapped_156
      (coe
         MAlonzo.Code.Data.List.Base.du_foldl_230
         (coe
            (\ v1 v2 ->
               coe
                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2) (coe v1)))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (let v1 = 8 :: Integer in
             coe
               (let v2
                      = coe
                          MAlonzo.Code.Induction.WellFounded.du_wfRecBuilder_160
                          (coe
                             (\ v2 ->
                                let v3 = 8 :: Integer in
                                coe
                                  (\ v4 ->
                                     let v5
                                           = coe
                                               MAlonzo.Code.Data.Nat.Base.du__'47'__318 (coe v2)
                                               (coe (10 :: Integer)) in
                                     coe
                                       (let v6
                                              = coe
                                                  MAlonzo.Code.Data.Nat.DivMod.du__mod__1162
                                                  (coe v2) (coe (10 :: Integer)) in
                                        coe
                                          (case coe v5 of
                                             0 -> coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe
                                                       MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                                                       (coe v6))
                                                    erased
                                             _ -> let v7 = subInt (coe v5) (coe (1 :: Integer)) in
                                                  coe
                                                    (coe
                                                       MAlonzo.Code.Data.Digit.du_cons_106 (coe v6)
                                                       (coe
                                                          v4 v5
                                                          (coe
                                                             MAlonzo.Code.Data.Digit.du_lem_144
                                                             (coe v7) (coe v3)
                                                             (coe
                                                                MAlonzo.Code.Data.Fin.Base.du_toℕ_18
                                                                (coe v6)))))))))) in
                coe
                  (let v3 = quotInt (coe v0) (coe (10 :: Integer)) in
                   coe
                     (let v4
                            = coe
                                MAlonzo.Code.Data.Nat.DivMod.du__mod__1162 (coe v0)
                                (coe (10 :: Integer)) in
                      coe
                        (case coe v3 of
                           0 -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                  (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v4)) erased
                           _ -> let v5 = subInt (coe v3) (coe (1 :: Integer)) in
                                coe
                                  (coe
                                     MAlonzo.Code.Data.Digit.du_cons_106 (coe v4)
                                     (coe
                                        v2 v3
                                        (coe
                                           MAlonzo.Code.Data.Digit.du_lem_144 (coe v5) (coe v1)
                                           (coe
                                              MAlonzo.Code.Data.Fin.Base.du_toℕ_18
                                              (coe v4))))))))))))
-- Once.Target.SymbolInjective.∨-true-split
d_'8744''45'true'45'split_172 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8744''45'true'45'split_172 v0 v1 ~v2
  = du_'8744''45'true'45'split_172 v0 v1
du_'8744''45'true'45'split_172 ::
  Bool -> Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8744''45'true'45'split_172 v0 v1
  = if coe v0
      then coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      else coe
             seq (coe v1) (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased)
-- Once.Target.SymbolInjective.identStart⇒¬digit
d_identStart'8658''172'digit_178 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identStart'8658''172'digit_178 = erased
-- Once.Target.SymbolInjective._.go
d_go_188 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_188 = erased
-- Once.Target.SymbolInjective.HeadNotDigit
d_HeadNotDigit_194 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> ()
d_HeadNotDigit_194 = erased
-- Once.Target.SymbolInjective.digit-prefix-unique
d_digit'45'prefix'45'unique_206 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_digit'45'prefix'45'unique_206 v0 v1 ~v2 ~v3 v4 v5 ~v6 ~v7 v8
  = du_digit'45'prefix'45'unique_206 v0 v1 v4 v5 v8
du_digit'45'prefix'45'unique_206 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_digit'45'prefix'45'unique_206 v0 v1 v2 v3 v4
  = case coe v0 of
      []
        -> case coe v1 of
             []
               -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v4)
             (:) v5 v6
               -> coe
                    seq (coe v3) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v5 v6
        -> case coe v1 of
             []
               -> coe
                    seq (coe v2) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
             (:) v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v11 v12
                      -> case coe v3 of
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v15 v16
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                     (coe
                                        du_digit'45'prefix'45'unique_206 (coe v6) (coe v8) (coe v12)
                                        (coe v16) erased))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.SymbolInjective.len-prefix-cancel
d_len'45'prefix'45'cancel_280 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_len'45'prefix'45'cancel_280 v0 v1 ~v2 ~v3 ~v4 v5
  = du_len'45'prefix'45'cancel_280 v0 v1 v5
du_len'45'prefix'45'cancel_280 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_len'45'prefix'45'cancel_280 v0 v1 v2
  = case coe v0 of
      []
        -> coe
             seq (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v2))
      (:) v3 v4
        -> case coe v1 of
             (:) v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                       (coe du_len'45'prefix'45'cancel_280 (coe v4) (coe v6) erased))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.SymbolInjective._.cong-pred
d_cong'45'pred_312 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong'45'pred_312 = erased
-- Once.Target.SymbolInjective.zenc++-nonempty
d_zenc'43''43''45'nonempty_326 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_zenc'43''43''45'nonempty_326 = erased
-- Once.Target.SymbolInjective.gen-split
d_gen'45'split_368 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_gen'45'split_368 ~v0 ~v1 ~v2 ~v3 ~v4 = du_gen'45'split_368
du_gen'45'split_368 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_gen'45'split_368
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe MAlonzo.Code.Data.List.Properties.du_'8759''45'injective_48))
-- Once.Target.SymbolInjective.consStep
d_consStep_394 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_consStep_394 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 = du_consStep_394 v4 v5
du_consStep_394 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_consStep_394 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           seq (coe v6)
                           (case coe v1 of
                              MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
                                -> case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                       -> case coe v9 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                              -> coe
                                                   seq (coe v11)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      erased
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                         (coe
                                                            MAlonzo.Code.Data.List.Properties.du_'8759''45'injective_48)))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
                                -> case coe v7 of
                                     MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
                                       -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                     MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                                       -> coe
                                            seq (coe v8)
                                            (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
               -> case coe v1 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
                      -> case coe v4 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                             -> case coe v6 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                    -> coe
                                         seq (coe v8)
                                         (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
                      -> case coe v4 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
                             -> coe du_gen'45'split_368
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
                             -> coe
                                  seq (coe v5) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
               -> coe
                    seq (coe v3)
                    (case coe v1 of
                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
                         -> case coe v4 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                                -> coe
                                     seq (coe v6) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
                         -> case coe v4 of
                              MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
                                -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                              MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
                                -> coe
                                     seq (coe v5)
                                     (coe
                                        MAlonzo.Code.Data.List.Properties.du_'8759''45'injective_48)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.SymbolInjective.zencL-inj
d_zencL'45'inj_608 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zencL'45'inj_608 = erased
-- Once.Target.SymbolInjective.ValidIdentChars
d_ValidIdentChars_638 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> ()
d_ValidIdentChars_638 = erased
-- Once.Target.SymbolInjective.mangL
d_mangL_646 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_mangL_646 v0
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe
         MAlonzo.Code.Data.Nat.Show.du_charsInBase_64 (coe (10 :: Integer))
         (coe
            MAlonzo.Code.Data.List.Base.du_length_268 (coe d_zencL_142 v0)))
      (coe d_zencL_142 v0)
-- Once.Target.SymbolInjective.zencL-vic
d_zencL'45'vic_656 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zencL'45'vic_656 v0 v1
  = case coe v0 of
      (:) v2 v3
        -> coe
             seq (coe v1)
             (coe du_go_672 (coe v2) (coe v3) (coe d_zec'45'class_138 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.SymbolInjective._.go
d_go_672 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_672 v0 v1 ~v2 ~v3 v4 = du_go_672 v0 v1 v4
du_go_672 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_672 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    seq (coe v5)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe 'z')
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4)
                             (coe d_zencL_142 v1))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> case coe v3 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe 'z')
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe 'u')
                             (coe
                                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                (coe
                                   MAlonzo.Code.Data.Nat.Show.du_charsInBase_64
                                   (coe (10 :: Integer))
                                   (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v0))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '_')
                                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                          (coe d_zencL_142 v1))
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    seq (coe v4)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe d_zencL_142 v1)
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.SymbolInjective.zencL-suffix-headND
d_zencL'45'suffix'45'headND_692 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> AgdaAny -> AgdaAny
d_zencL'45'suffix'45'headND_692 v0 ~v1 v2
  = du_zencL'45'suffix'45'headND_692 v0 v2
du_zencL'45'suffix'45'headND_692 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> AgdaAny -> AgdaAny
du_zencL'45'suffix'45'headND_692 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe d_zencL'45'vic_656 (coe v0) (coe v1))))
-- Once.Target.SymbolInjective.++-cons-≢[]
d_'43''43''45'cons'45''8802''91''93'_716 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'43''43''45'cons'45''8802''91''93'_716 = erased
-- Once.Target.SymbolInjective.mangL-nonempty
d_mangL'45'nonempty_724 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_mangL'45'nonempty_724 = erased
-- Once.Target.SymbolInjective.joinUsL'
d_joinUsL''_740 ::
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_joinUsL''_740 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
             (coe d_withSep_742 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.SymbolInjective.withSep
d_withSep_742 ::
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_withSep_742 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '_')
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
                (coe d_withSep_742 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.SymbolInjective.peel
d_peel_760 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_peel_760 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_peel_760 v0 v1
du_peel_760 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_peel_760 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            du_len'45'prefix'45'cancel_280 (coe d_zencL_142 v0)
            (coe d_zencL_142 v1) erased))
-- Once.Target.SymbolInjective.withSep-inj
d_withSep'45'inj_792 ::
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]] ->
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_withSep'45'inj_792 = erased
-- Once.Target.SymbolInjective.joinL-inj
d_joinL'45'inj_846 ::
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]] ->
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_joinL'45'inj_846 = erased
-- Once.Target.SymbolInjective.ValidIdent
d_ValidIdent_896 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d_ValidIdent_896 = erased
-- Once.Target.SymbolInjective.toList-showNat
d_toList'45'showNat_902 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toList'45'showNat_902 = erased
-- Once.Target.SymbolInjective.toList-zencode
d_toList'45'zencode_908 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toList'45'zencode_908 = erased
-- Once.Target.SymbolInjective.toList-mangle
d_toList'45'mangle_914 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toList'45'mangle_914 = erased
-- Once.Target.SymbolInjective._.L
d_L_922 :: MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Integer
d_L_922 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_length_268
      (coe
         MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
         (MAlonzo.Code.Once.Target.Symbol.d_z'45'encode_40 (coe v0)))
-- Once.Target.SymbolInjective.toList-joinUs
d_toList'45'joinUs_926 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toList'45'joinUs_926 = erased
-- Once.Target.SymbolInjective.body-rel
d_body'45'rel_946 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_body'45'rel_946 = erased
-- Once.Target.SymbolInjective.once-symbol-path-injective
d_once'45'symbol'45'path'45'injective_954 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_once'45'symbol'45'path'45'injective_954 = erased
-- Once.Target.SymbolInjective._.M
d_M_970 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_M_970 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_M_970 v5
du_M_970 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_M_970 v0
  = coe
      MAlonzo.Code.Once.Target.Symbol.d_join'45'us_48
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe MAlonzo.Code.Once.Target.Symbol.d_mangle'45'component_44)
         (coe MAlonzo.Code.Once.CanonicalName.d_parts_8 (coe v0)))
-- Once.Target.SymbolInjective._.teq
d_teq_974 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_teq_974 = erased
-- Once.Target.SymbolInjective._.bodyEq
d_bodyEq_976 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bodyEq_976 = erased
-- Once.Target.SymbolInjective.once-symbol-own-injective
d_once'45'symbol'45'own'45'injective_986 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_once'45'symbol'45'own'45'injective_986 = erased
-- Once.Target.SymbolInjective.once-symbol-own-≢
d_once'45'symbol'45'own'45''8802'_1002 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_once'45'symbol'45'own'45''8802'_1002 = erased
