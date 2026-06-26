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
-- Once.Target.SymbolInjective.ZClass
d_ZClass_46 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> ()
d_ZClass_46 = erased
-- Once.Target.SymbolInjective.zec-class-aux
d_zec'45'class'45'aux_70 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_zec'45'class'45'aux_70 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_zec'45'class'45'aux_70 v1 v2 v3 v4 v5 v6 v7
du_zec'45'class'45'aux_70 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_zec'45'class'45'aux_70 v0 v1 v2 v3 v4 v5 v6
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
        -> if coe v7
             then coe
                    seq (coe v8)
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe 'z')
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)))
             else coe
                    seq (coe v8)
                    (case coe v1 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                         -> if coe v9
                              then coe
                                     seq (coe v10)
                                     (coe
                                        MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe 'q')
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                              erased)))
                              else coe
                                     seq (coe v10)
                                     (case coe v2 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                          -> if coe v11
                                               then coe
                                                      seq (coe v12)
                                                      (coe
                                                         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe 'p')
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               erased erased)))
                                               else coe
                                                      seq (coe v12)
                                                      (case coe v3 of
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                           -> if coe v13
                                                                then coe
                                                                       seq (coe v14)
                                                                       (coe
                                                                          MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe 't')
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                erased erased)))
                                                                else coe
                                                                       seq (coe v14)
                                                                       (case coe v4 of
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                                                            -> if coe v15
                                                                                 then coe
                                                                                        seq
                                                                                        (coe v16)
                                                                                        (coe
                                                                                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                                                                           (coe
                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                              (coe
                                                                                                 'b')
                                                                                              (coe
                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                 erased
                                                                                                 erased)))
                                                                                 else coe
                                                                                        seq
                                                                                        (coe v16)
                                                                                        (case coe
                                                                                                v5 of
                                                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                                                             -> if coe
                                                                                                     v17
                                                                                                  then coe
                                                                                                         seq
                                                                                                         (coe
                                                                                                            v18)
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                               (coe
                                                                                                                  'h')
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                  erased
                                                                                                                  erased)))
                                                                                                  else coe
                                                                                                         seq
                                                                                                         (coe
                                                                                                            v18)
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
                                                                                                                             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                (coe
                                                                                                                                   'd')
                                                                                                                                (coe
                                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                   erased
                                                                                                                                   erased)))
                                                                                                                   else coe
                                                                                                                          seq
                                                                                                                          (coe
                                                                                                                             v20)
                                                                                                                          (coe
                                                                                                                             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                erased
                                                                                                                                erased))
                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.SymbolInjective.zec-class
d_zec'45'class_106 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_zec'45'class_106 v0
  = coe
      du_zec'45'class'45'aux_70
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
-- Once.Target.SymbolInjective.zencL
d_zencL_110 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_zencL_110
  = coe
      MAlonzo.Code.Data.List.Base.du_concatMap_246
      (coe MAlonzo.Code.Once.Target.Symbol.d_z'45'encode'45'char_30)
-- Once.Target.SymbolInjective.cons≢[]
d_cons'8802''91''93'_118 ::
  () ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_cons'8802''91''93'_118 = erased
-- Once.Target.SymbolInjective.zenc++-nonempty
d_zenc'43''43''45'nonempty_124 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_zenc'43''43''45'nonempty_124 = erased
-- Once.Target.SymbolInjective.consStep
d_consStep_156 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_consStep_156 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 = du_consStep_156 v4 v5
du_consStep_156 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_consStep_156 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> coe
                    seq (coe v4)
                    (case coe v1 of
                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
                         -> case coe v5 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                -> coe
                                     seq (coe v7)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                           (coe
                                              MAlonzo.Code.Data.List.Properties.du_'8759''45'injective_48)))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
                         -> coe
                              seq (coe v5) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> coe
             seq (coe v2)
             (case coe v1 of
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
                  -> case coe v3 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                         -> coe
                              seq (coe v5) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
                  -> coe
                       seq (coe v3)
                       (coe MAlonzo.Code.Data.List.Properties.du_'8759''45'injective_48)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.SymbolInjective.zencL-inj
d_zencL'45'inj_268 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zencL'45'inj_268 = erased
-- Once.Target.SymbolInjective.false≢true
d_false'8802'true_298 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_false'8802'true_298 = erased
-- Once.Target.SymbolInjective.all-digits-mapped
d_all'45'digits'45'mapped_302 ::
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_all'45'digits'45'mapped_302 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
             (d_all'45'digits'45'mapped_302 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.SymbolInjective.charsInBase-all-digits
d_charsInBase'45'all'45'digits_310 ::
  Integer -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_charsInBase'45'all'45'digits_310 v0
  = coe
      d_all'45'digits'45'mapped_302
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
d_'8744''45'true'45'split_318 ::
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8744''45'true'45'split_318 v0 v1 ~v2
  = du_'8744''45'true'45'split_318 v0 v1
du_'8744''45'true'45'split_318 ::
  Bool -> Bool -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8744''45'true'45'split_318 v0 v1
  = if coe v0
      then coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      else coe
             seq (coe v1) (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased)
-- Once.Target.SymbolInjective.identStart⇒¬digit
d_identStart'8658''172'digit_324 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identStart'8658''172'digit_324 = erased
-- Once.Target.SymbolInjective._.go
d_go_334 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_334 = erased
-- Once.Target.SymbolInjective.HeadNotDigit
d_HeadNotDigit_340 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> ()
d_HeadNotDigit_340 = erased
-- Once.Target.SymbolInjective.digit-prefix-unique
d_digit'45'prefix'45'unique_352 ::
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
d_digit'45'prefix'45'unique_352 v0 v1 ~v2 ~v3 v4 v5 ~v6 ~v7 v8
  = du_digit'45'prefix'45'unique_352 v0 v1 v4 v5 v8
du_digit'45'prefix'45'unique_352 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_digit'45'prefix'45'unique_352 v0 v1 v2 v3 v4
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
                                        du_digit'45'prefix'45'unique_352 (coe v6) (coe v8) (coe v12)
                                        (coe v16) erased))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.SymbolInjective.len-prefix-cancel
d_len'45'prefix'45'cancel_426 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_len'45'prefix'45'cancel_426 v0 v1 ~v2 ~v3 ~v4 v5
  = du_len'45'prefix'45'cancel_426 v0 v1 v5
du_len'45'prefix'45'cancel_426 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_len'45'prefix'45'cancel_426 v0 v1 v2
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
                       (coe du_len'45'prefix'45'cancel_426 (coe v4) (coe v6) erased))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.SymbolInjective._.cong-pred
d_cong'45'pred_458 ::
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
d_cong'45'pred_458 = erased
-- Once.Target.SymbolInjective.ValidIdentChars
d_ValidIdentChars_468 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> ()
d_ValidIdentChars_468 = erased
-- Once.Target.SymbolInjective.mangL
d_mangL_476 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_mangL_476 v0
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe
         MAlonzo.Code.Data.Nat.Show.du_charsInBase_64 (coe (10 :: Integer))
         (coe
            MAlonzo.Code.Data.List.Base.du_length_268 (coe d_zencL_110 v0)))
      (coe d_zencL_110 v0)
-- Once.Target.SymbolInjective.zencL-vic
d_zencL'45'vic_486 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zencL'45'vic_486 v0 v1
  = case coe v0 of
      (:) v2 v3
        -> coe
             seq (coe v1)
             (coe du_go_502 (coe v2) (coe v3) (coe d_zec'45'class_106 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.SymbolInjective._.go
d_go_502 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_502 v0 v1 ~v2 ~v3 v4 = du_go_502 v0 v1 v4
du_go_502 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_502 v0 v1 v2
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
                             (coe d_zencL_110 v1))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> coe
             seq (coe v3)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe d_zencL_110 v1)
                   (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.SymbolInjective.zencL-suffix-headND
d_zencL'45'suffix'45'headND_518 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> AgdaAny -> AgdaAny
d_zencL'45'suffix'45'headND_518 v0 ~v1 v2
  = du_zencL'45'suffix'45'headND_518 v0 v2
du_zencL'45'suffix'45'headND_518 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] -> AgdaAny -> AgdaAny
du_zencL'45'suffix'45'headND_518 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe d_zencL'45'vic_486 (coe v0) (coe v1))))
-- Once.Target.SymbolInjective.++-cons-≢[]
d_'43''43''45'cons'45''8802''91''93'_542 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'43''43''45'cons'45''8802''91''93'_542 = erased
-- Once.Target.SymbolInjective.mangL-nonempty
d_mangL'45'nonempty_550 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_mangL'45'nonempty_550 = erased
-- Once.Target.SymbolInjective.joinUsL'
d_joinUsL''_566 ::
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_joinUsL''_566 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
             (coe d_withSep_568 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.SymbolInjective.withSep
d_withSep_568 ::
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_withSep_568 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '_')
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
                (coe d_withSep_568 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Target.SymbolInjective.peel
d_peel_586 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_peel_586 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_peel_586 v0 v1
du_peel_586 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_peel_586 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            du_len'45'prefix'45'cancel_426 (coe d_zencL_110 v0)
            (coe d_zencL_110 v1) erased))
-- Once.Target.SymbolInjective.withSep-inj
d_withSep'45'inj_618 ::
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]] ->
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_withSep'45'inj_618 = erased
-- Once.Target.SymbolInjective.joinL-inj
d_joinL'45'inj_672 ::
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]] ->
  [[MAlonzo.Code.Agda.Builtin.Char.T_Char_6]] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_joinL'45'inj_672 = erased
-- Once.Target.SymbolInjective.ValidIdent
d_ValidIdent_722 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d_ValidIdent_722 = erased
-- Once.Target.SymbolInjective.toList-showNat
d_toList'45'showNat_728 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toList'45'showNat_728 = erased
-- Once.Target.SymbolInjective.toList-zencode
d_toList'45'zencode_734 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toList'45'zencode_734 = erased
-- Once.Target.SymbolInjective.toList-mangle
d_toList'45'mangle_740 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toList'45'mangle_740 = erased
-- Once.Target.SymbolInjective._.L
d_L_748 :: MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Integer
d_L_748 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_length_268
      (coe
         MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
         (MAlonzo.Code.Once.Target.Symbol.d_z'45'encode_34 (coe v0)))
-- Once.Target.SymbolInjective.toList-joinUs
d_toList'45'joinUs_752 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toList'45'joinUs_752 = erased
-- Once.Target.SymbolInjective.body-rel
d_body'45'rel_772 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_body'45'rel_772 = erased
-- Once.Target.SymbolInjective.once-symbol-path-injective
d_once'45'symbol'45'path'45'injective_780 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_once'45'symbol'45'path'45'injective_780 = erased
-- Once.Target.SymbolInjective._.M
d_M_796 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_M_796 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_M_796 v5
du_M_796 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_M_796 v0
  = coe
      MAlonzo.Code.Once.Target.Symbol.d_join'45'us_42
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe MAlonzo.Code.Once.Target.Symbol.d_mangle'45'component_38)
         (coe MAlonzo.Code.Once.CanonicalName.d_parts_8 (coe v0)))
-- Once.Target.SymbolInjective._.teq
d_teq_800 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_teq_800 = erased
-- Once.Target.SymbolInjective._.bodyEq
d_bodyEq_802 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_bodyEq_802 = erased
-- Once.Target.SymbolInjective.once-symbol-own-injective
d_once'45'symbol'45'own'45'injective_812 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_once'45'symbol'45'own'45'injective_812 = erased
-- Once.Target.SymbolInjective.once-symbol-own-≢
d_once'45'symbol'45'own'45''8802'_828 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_once'45'symbol'45'own'45''8802'_828 = erased
