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

module MAlonzo.Code.Once.Adequacy.ResolveBridge where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Module.Resolve
import qualified MAlonzo.Code.Once.Spec.Resolution
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Adequacy.ResolveBridge.elemStr-complete
d_elemStr'45'complete_10 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_elemStr'45'complete_10 = erased
-- Once.Adequacy.ResolveBridge.∉⇒elemStr-false
d_'8713''8658'elemStr'45'false_68 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8713''8658'elemStr'45'false_68 = erased
-- Once.Adequacy.ResolveBridge.elemStr-sound
d_elemStr'45'sound_108 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_elemStr'45'sound_108 v0 v1 ~v2 = du_elemStr'45'sound_108 v0 v1
du_elemStr'45'sound_108 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_elemStr'45'sound_108 v0 v1
  = case coe v1 of
      (:) v2 v3
        -> let v4
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     erased
                     (\ v4 ->
                        coe
                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                          (coe v0))
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                        (coe v2)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                  -> if coe v5
                       then coe
                              seq (coe v6)
                              (coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 erased)
                       else coe
                              seq (coe v6)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                 (coe du_elemStr'45'sound_108 (coe v0) (coe v3)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ResolveBridge.elemStr-false⇒∉
d_elemStr'45'false'8658''8713'_142 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_elemStr'45'false'8658''8713'_142 = erased
-- Once.Adequacy.ResolveBridge.lookupUn-complete
d_lookupUn'45'complete_192 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Spec.Resolution.T_FirstAt_18 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookupUn'45'complete_192 = erased
-- Once.Adequacy.ResolveBridge.lookupUn-absent
d_lookupUn'45'absent_280 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookupUn'45'absent_280 = erased
-- Once.Adequacy.ResolveBridge.lookupUn-sound
d_lookupUn'45'sound_330 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Resolution.T_FirstAt_18
d_lookupUn'45'sound_330 v0 v1 ~v2 ~v3
  = du_lookupUn'45'sound_330 v0 v1
du_lookupUn'45'sound_330 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Resolution.T_FirstAt_18
du_lookupUn'45'sound_330 v0 v1
  = case coe v0 of
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> let v6
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v6 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe v1))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v1)
                               (coe v4)) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                         -> if coe v7
                              then coe
                                     seq (coe v8)
                                     (coe MAlonzo.Code.Once.Spec.Resolution.C_fa'45'here_30)
                              else coe
                                     seq (coe v8)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Resolution.C_fa'45'there_38
                                        (coe du_lookupUn'45'sound_330 (coe v3) (coe v1)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ResolveBridge.lookupUn-nothing
d_lookupUn'45'nothing_376 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_lookupUn'45'nothing_376 v0 v1 ~v2
  = du_lookupUn'45'nothing_376 v0 v1
du_lookupUn'45'nothing_376 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_lookupUn'45'nothing_376 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> let v6
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v6 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe v1))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v1)
                               (coe v4)) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                         -> coe
                              seq (coe v7)
                              (coe
                                 seq (coe v8)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
                                    (coe du_lookupUn'45'nothing_376 (coe v3) (coe v1))))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ResolveBridge.lookupAl-complete
d_lookupAl'45'complete_422 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Spec.Resolution.T_FirstAt_18 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookupAl'45'complete_422 = erased
-- Once.Adequacy.ResolveBridge.lookupAl-absent
d_lookupAl'45'absent_512 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookupAl'45'absent_512 = erased
-- Once.Adequacy.ResolveBridge.lookupAl-sound
d_lookupAl'45'sound_564 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Resolution.T_FirstAt_18
d_lookupAl'45'sound_564 v0 v1 ~v2 ~v3
  = du_lookupAl'45'sound_564 v0 v1
du_lookupAl'45'sound_564 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Resolution.T_FirstAt_18
du_lookupAl'45'sound_564 v0 v1
  = case coe v0 of
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> let v6
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v6 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe v4))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v4)
                               (coe v1)) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                         -> if coe v7
                              then coe
                                     seq (coe v8)
                                     (coe MAlonzo.Code.Once.Spec.Resolution.C_fa'45'here_30)
                              else coe
                                     seq (coe v8)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Resolution.C_fa'45'there_38
                                        (coe du_lookupAl'45'sound_564 (coe v3) (coe v1)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ResolveBridge.lookupAl-nothing
d_lookupAl'45'nothing_606 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_lookupAl'45'nothing_606 v0 v1 ~v2
  = du_lookupAl'45'nothing_606 v0 v1
du_lookupAl'45'nothing_606 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_lookupAl'45'nothing_606 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> let v6
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v6 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe v4))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v4)
                               (coe v1)) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                         -> coe
                              seq (coe v7)
                              (coe
                                 seq (coe v8)
                                 (coe
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
                                    (coe du_lookupAl'45'nothing_606 (coe v3) (coe v1))))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ResolveBridge.expandPath-complete
d_expandPath'45'complete_648 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Spec.Resolution.T_ExpandsTo_50 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_expandPath'45'complete_648 = erased
-- Once.Adequacy.ResolveBridge.expandPath-sound
d_expandPath'45'sound_688 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Spec.Resolution.T_ExpandsTo_50
d_expandPath'45'sound_688 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Once.Spec.Resolution.C_ex'45'nil_52
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     erased
                     (\ v3 ->
                        coe
                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                          (coe v1))
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v1)
                        (coe ("I" :: Data.Text.Text))) in
           coe
             (case coe v3 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
                  -> if coe v4
                       then coe
                              seq (coe v5) (coe MAlonzo.Code.Once.Spec.Resolution.C_ex'45'I_56)
                       else coe
                              seq (coe v5)
                              (coe MAlonzo.Code.Once.Spec.Resolution.C_ex'45'other_62)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ResolveBridge.GenWord-isBuiltinName
d_GenWord'45'isBuiltinName_710 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_GenWord'45'isBuiltinName_710 = erased
-- Once.Adequacy.ResolveBridge.resolvesVar-sound
d_resolvesVar'45'sound_738 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Resolution.T_ResolvesVar_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolvesVar'45'sound_738 = erased
-- Once.Adequacy.ResolveBridge.resolvesVar-complete
d_resolvesVar'45'complete_830 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Resolution.T_ResolvesVar_68
d_resolvesVar'45'complete_830 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.Parser.Module.Resolve.d_elemStr_236
              (coe v2) (coe v0) in
    coe
      (if coe v3
         then coe
                MAlonzo.Code.Once.Spec.Resolution.C_rv'45'binder_76
                (coe du_elemStr'45'sound_108 (coe v2) (coe v0))
         else (let v4
                     = coe
                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                         (coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            (coe MAlonzo.Code.Data.List.Relation.Unary.Any.du_fromSum_132)
                            (coe MAlonzo.Code.Data.List.Relation.Unary.Any.du_toSum_126)
                            (coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'8846''45'dec__96
                               (coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                  erased
                                  (\ v4 ->
                                     coe
                                       MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                       (coe v2))
                                  (coe
                                     MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                                     (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                                     (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v2)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                        ("id" :: Data.Text.Text))))
                               (coe
                                  MAlonzo.Code.Data.List.Relation.Unary.Any.du_any'63'_138
                                  (coe
                                     (\ v4 ->
                                        coe
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                          erased
                                          (\ v5 ->
                                             coe
                                               MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                               (coe v2))
                                          (coe
                                             MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                             (coe v2) (coe v4))))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                     (coe ("fst" :: Data.Text.Text))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                        (coe ("snd" :: Data.Text.Text))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                           (coe ("inl" :: Data.Text.Text))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe ("inr" :: Data.Text.Text))
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                 (coe ("unit" :: Data.Text.Text))
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                    (coe ("pair" :: Data.Text.Text))
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                       (coe ("terminal" :: Data.Text.Text))
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                          (coe ("initial" :: Data.Text.Text))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                             (coe ("curry" :: Data.Text.Text))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                (coe ("apply" :: Data.Text.Text))
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                   (coe
                                                                      ("compose" :: Data.Text.Text))
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                      (coe
                                                                         ("case" :: Data.Text.Text))
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                         (coe
                                                                            ("cata"
                                                                             ::
                                                                             Data.Text.Text))
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                            (coe
                                                                               ("ana"
                                                                                ::
                                                                                Data.Text.Text))
                                                                            (coe
                                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                               (coe
                                                                                  ("In"
                                                                                   ::
                                                                                   Data.Text.Text))
                                                                               (coe
                                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                  (coe
                                                                                     ("Out"
                                                                                      ::
                                                                                      Data.Text.Text))
                                                                                  (coe
                                                                                     MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))))) in
               coe
                 (if coe v4
                    then coe
                           MAlonzo.Code.Once.Spec.Resolution.C_rv'45'gen_80
                           (coe
                              MAlonzo.Code.Once.Parser.Module.Resolve.du_isBuiltinName'45'sound_198
                              (coe v2))
                    else (let v5
                                = MAlonzo.Code.Once.Parser.Module.Resolve.d_lookupUnaliased_162
                                    (coe v1) (coe v2) in
                          coe
                            (case coe v5 of
                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                 -> coe
                                      MAlonzo.Code.Once.Spec.Resolution.C_rv'45'import_88 v6
                                      (MAlonzo.Code.Once.Parser.Module.Resolve.d_expandPath_360
                                         (coe v6))
                                      (coe du_lookupUn'45'sound_330 (coe v1) (coe v2))
                                      (d_expandPath'45'sound_688 (coe v6))
                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                 -> coe
                                      MAlonzo.Code.Once.Spec.Resolution.C_rv'45'own_92
                                      (coe du_lookupUn'45'nothing_376 (coe v1) (coe v2))
                               _ -> MAlonzo.RTE.mazUnreachableError)))))
-- Once.Adequacy.ResolveBridge.resolves-sound
d_resolves'45'sound_904 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Resolution.T_ResolvesExpr_98 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolves'45'sound_904 = erased
-- Once.Adequacy.ResolveBridge._.cong₃
d_cong'8323'_1038 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Resolution.T_ResolvesExpr_98 ->
  MAlonzo.Code.Once.Spec.Resolution.T_ResolvesExpr_98 ->
  MAlonzo.Code.Once.Spec.Resolution.T_ResolvesExpr_98 ->
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong'8323'_1038 = erased
-- Once.Adequacy.ResolveBridge.resolves-complete
d_resolves'45'complete_1124 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Spec.Resolution.T_ResolvesExpr_98
d_resolves'45'complete_1124 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v4
        -> coe
             MAlonzo.Code.Once.Spec.Resolution.C_re'45'var_110
             (d_resolvesVar'45'complete_830 (coe v2) (coe v0) (coe v4))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v4 v5
        -> let v6
                 = MAlonzo.Code.Once.Parser.Module.Resolve.d_lookupImportAlias_90
                     (coe v1) (coe v5) in
           coe
             (case coe v6 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                  -> coe
                       MAlonzo.Code.Once.Spec.Resolution.C_re'45'qual_122 v7
                       (MAlonzo.Code.Once.Parser.Module.Resolve.d_expandPath_360 (coe v7))
                       (coe du_lookupAl'45'sound_564 (coe v1) (coe v5))
                       (d_expandPath'45'sound_688 (coe v7))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       MAlonzo.Code.Once.Spec.Resolution.C_re'45'qual'45'unknown_130
                       (coe du_lookupAl'45'nothing_606 (coe v1) (coe v5))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v4
        -> coe MAlonzo.Code.Once.Spec.Resolution.C_re'45'res_136
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Resolution.C_re'45'app_148
             (d_resolves'45'complete_1124 (coe v0) (coe v1) (coe v2) (coe v4))
             (d_resolves'45'complete_1124 (coe v0) (coe v1) (coe v2) (coe v5))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Resolution.C_re'45'lam_158
             (d_resolves'45'complete_1124
                (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4) (coe v2))
                (coe v5))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Spec.Resolution.C_re'45'let_172
             (d_resolves'45'complete_1124 (coe v0) (coe v1) (coe v2) (coe v5))
             (d_resolves'45'complete_1124
                (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4) (coe v2))
                (coe v6))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Resolution.C_re'45'pair_184
             (d_resolves'45'complete_1124 (coe v0) (coe v1) (coe v2) (coe v4))
             (d_resolves'45'complete_1124 (coe v0) (coe v1) (coe v2) (coe v5))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v4 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.Spec.Resolution.C_re'45'destruct_204
             (d_resolves'45'complete_1124 (coe v0) (coe v1) (coe v2) (coe v4))
             (d_resolves'45'complete_1124
                (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5) (coe v2))
                (coe v6))
             (d_resolves'45'complete_1124
                (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v7) (coe v2))
                (coe v8))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_52
        -> coe MAlonzo.Code.Once.Spec.Resolution.C_re'45'unit_252
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v4
        -> coe MAlonzo.Code.Once.Spec.Resolution.C_re'45'int_258
      MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v4 v5 v6 v7
        -> coe MAlonzo.Code.Once.Spec.Resolution.C_re'45'float_270
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_58 v4
        -> coe MAlonzo.Code.Once.Spec.Resolution.C_re'45'str_276
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Resolution.C_re'45'annot_214
             (d_resolves'45'complete_1124 (coe v0) (coe v1) (coe v2) (coe v4))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Spec.Resolution.C_re'45'binop_228
             (d_resolves'45'complete_1124 (coe v0) (coe v1) (coe v2) (coe v5))
             (d_resolves'45'complete_1124 (coe v0) (coe v1) (coe v2) (coe v6))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v5
        -> coe
             MAlonzo.Code.Once.Spec.Resolution.C_re'45'unop_238
             (d_resolves'45'complete_1124 (coe v0) (coe v1) (coe v2) (coe v5))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAna_66 v4 v5
        -> coe
             MAlonzo.Code.Once.Spec.Resolution.C_re'45'ana_248
             (d_resolves'45'complete_1124 (coe v0) (coe v1) (coe v2) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ResolveBridge.resolvesDecl-sound
d_resolvesDecl'45'sound_1326 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32 ->
  MAlonzo.Code.Once.Spec.Resolution.T_ResolvesDecl_284 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolvesDecl'45'sound_1326 = erased
-- Once.Adequacy.ResolveBridge.resolvesDecl-complete
d_resolvesDecl'45'complete_1372 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32 ->
  MAlonzo.Code.Once.Spec.Resolution.T_ResolvesDecl_284
d_resolvesDecl'45'complete_1372 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34 v4 v5
        -> coe MAlonzo.Code.Once.Spec.Resolution.C_rd'45'typesig_306
      MAlonzo.Code.Once.Parser.Module.Core.C_DFunDef_36 v4 v5 v6
        -> coe
             MAlonzo.Code.Once.Spec.Resolution.C_rd'45'fundef_300
             (d_resolves'45'complete_1124 (coe v1) (coe v2) (coe v0) (coe v6))
      MAlonzo.Code.Once.Parser.Module.Core.C_DSignature_38 v4 v5 v6 v7
        -> coe MAlonzo.Code.Once.Spec.Resolution.C_rd'45'signature_316
      MAlonzo.Code.Once.Parser.Module.Core.C_DTypeAlias_40 v4 v5 v6
        -> coe MAlonzo.Code.Once.Spec.Resolution.C_rd'45'typealias_324
      MAlonzo.Code.Once.Parser.Module.Core.C_DImport_42 v4
        -> coe MAlonzo.Code.Once.Spec.Resolution.C_rd'45'import_328
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ResolveBridge.path≟-refl
d_path'8799''45'refl_1432 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_path'8799''45'refl_1432 = erased
-- Once.Adequacy.ResolveBridge.path≟-sound
d_path'8799''45'sound_1456 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_path'8799''45'sound_1456 = erased
-- Once.Adequacy.ResolveBridge.lookupMod-complete
d_lookupMod'45'complete_1498 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.Spec.Resolution.T_FirstAt_18 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookupMod'45'complete_1498 = erased
-- Once.Adequacy.ResolveBridge.import-red
d_import'45'red_1578 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Import_20 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_import'45'red_1578 = erased
-- Once.Adequacy.ResolveBridge._.go
d_go_1612 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Import_20 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_1612 = erased
-- Once.Adequacy.ResolveBridge.resolvesDecls-sound
d_resolvesDecls'45'sound_1646 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Once.Spec.Resolution.T_ResolvesDecls_372 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolvesDecls'45'sound_1646 = erased
-- Once.Adequacy.ResolveBridge.resolvesModule-sound
d_resolvesModule'45'sound_1762 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Once.Spec.Resolution.T_ResolvesModule_408 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolvesModule'45'sound_1762 = erased
-- Once.Adequacy.ResolveBridge.path≟-false⇒≢
d_path'8799''45'false'8658''8802'_1778 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_path'8799''45'false'8658''8802'_1778 = erased
-- Once.Adequacy.ResolveBridge.lookupMod-sound
d_lookupMod'45'sound_1798 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Resolution.T_FirstAt_18
d_lookupMod'45'sound_1798 v0 v1 ~v2 ~v3
  = du_lookupMod'45'sound_1798 v0 v1
du_lookupMod'45'sound_1798 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Spec.Resolution.T_FirstAt_18
du_lookupMod'45'sound_1798 v0 v1
  = case coe v0 of
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> let v6
                        = MAlonzo.Code.Once.Parser.Module.Resolve.d__path'8799'__10
                            (coe v4) (coe v1) in
                  coe
                    (if coe v6
                       then coe MAlonzo.Code.Once.Spec.Resolution.C_fa'45'here_30
                       else coe
                              MAlonzo.Code.Once.Spec.Resolution.C_fa'45'there_38
                              (coe du_lookupMod'45'sound_1798 (coe v3) (coe v1)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ResolveBridge.resolvesDecls-complete
d_resolvesDecls'45'complete_1854 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Resolution.T_ResolvesDecls_372
d_resolvesDecls'45'complete_1854 v0 v1 v2 v3 v4 ~v5 ~v6
  = du_resolvesDecls'45'complete_1854 v0 v1 v2 v3 v4
du_resolvesDecls'45'complete_1854 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Once.Spec.Resolution.T_ResolvesDecls_372
du_resolvesDecls'45'complete_1854 v0 v1 v2 v3 v4
  = case coe v4 of
      [] -> coe MAlonzo.Code.Once.Spec.Resolution.C_rds'45'nil_382
      (:) v5 v6
        -> case coe v5 of
             MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34 v7 v8
               -> coe
                    du_rdc'45'cons_1898 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
                    (coe MAlonzo.Code.Once.Spec.Resolution.C_nim'45'typesig_336)
                    (coe v6)
                    (coe
                       MAlonzo.Code.Once.Parser.Module.Resolve.d_resolveDecls_854 (coe v1)
                       (coe v2) (coe v3) (coe v0) (coe v6))
             MAlonzo.Code.Once.Parser.Module.Core.C_DFunDef_36 v7 v8 v9
               -> coe
                    du_rdc'45'cons_1898 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
                    (coe MAlonzo.Code.Once.Spec.Resolution.C_nim'45'fundef_344)
                    (coe v6)
                    (coe
                       MAlonzo.Code.Once.Parser.Module.Resolve.d_resolveDecls_854 (coe v1)
                       (coe v2) (coe v3) (coe v0) (coe v6))
             MAlonzo.Code.Once.Parser.Module.Core.C_DSignature_38 v7 v8 v9 v10
               -> coe
                    du_rdc'45'cons_1898 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
                    (coe MAlonzo.Code.Once.Spec.Resolution.C_nim'45'sig_354) (coe v6)
                    (coe
                       MAlonzo.Code.Once.Parser.Module.Resolve.d_resolveDecls_854 (coe v1)
                       (coe v2) (coe v3) (coe v0) (coe v6))
             MAlonzo.Code.Once.Parser.Module.Core.C_DTypeAlias_40 v7 v8 v9
               -> coe
                    du_rdc'45'cons_1898 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
                    (coe MAlonzo.Code.Once.Spec.Resolution.C_nim'45'alias_362) (coe v6)
                    (coe
                       MAlonzo.Code.Once.Parser.Module.Resolve.d_resolveDecls_854 (coe v1)
                       (coe v2) (coe v3) (coe v0) (coe v6))
             MAlonzo.Code.Once.Parser.Module.Core.C_DImport_42 v7
               -> coe
                    du_rdc'45'import_1878 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7)
                    (coe v6)
                    (coe
                       MAlonzo.Code.Once.Parser.Module.Resolve.d_lookupModule_40 (coe v0)
                       (coe MAlonzo.Code.Once.Parser.Module.Core.d_path_26 (coe v7)))
                    (coe
                       MAlonzo.Code.Once.Parser.Module.Resolve.d_resolveDecls_854 (coe v1)
                       (coe v2) (coe v3) (coe v0) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ResolveBridge.rdc-import
d_rdc'45'import_1878 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Import_20 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Resolution.T_ResolvesDecls_372
d_rdc'45'import_1878 v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 v9 ~v10 ~v11
  = du_rdc'45'import_1878 v0 v1 v2 v3 v4 v5 v7 v9
du_rdc'45'import_1878 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Import_20 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Resolution.T_ResolvesDecls_372
du_rdc'45'import_1878 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> case coe v8 of
             MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50 v9
               -> case coe v7 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                      -> coe
                           MAlonzo.Code.Once.Spec.Resolution.C_rds'45'import_402 v9 v10
                           (coe
                              du_lookupMod'45'sound_1798 (coe v0)
                              (coe MAlonzo.Code.Once.Parser.Module.Core.d_path_26 (coe v4)))
                           (coe
                              du_resolvesDecls'45'complete_1854 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ResolveBridge.rdc-cons
d_rdc'45'cons_1898 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32 ->
  MAlonzo.Code.Once.Spec.Resolution.T_NotImport_330 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Resolution.T_ResolvesDecls_372
d_rdc'45'cons_1898 v0 v1 v2 v3 v4 v5 v6 ~v7 v8 ~v9 ~v10
  = du_rdc'45'cons_1898 v0 v1 v2 v3 v4 v5 v6 v8
du_rdc'45'cons_1898 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32 ->
  MAlonzo.Code.Once.Spec.Resolution.T_NotImport_330 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Resolution.T_ResolvesDecls_372
du_rdc'45'cons_1898 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
        -> coe
             MAlonzo.Code.Once.Spec.Resolution.C_rds'45'cons_392 v5
             (d_resolvesDecl'45'complete_1372
                (coe v1) (coe v2) (coe v3) (coe v4))
             (coe
                du_resolvesDecls'45'complete_1854 (coe v0) (coe v1) (coe v2)
                (coe v3) (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ResolveBridge.resolveImports-ok
d_resolveImports'45'ok_2110 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveImports'45'ok_2110 = erased
-- Once.Adequacy.ResolveBridge.resolveImports-bad
d_resolveImports'45'bad_2130 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveImports'45'bad_2130 = erased
-- Once.Adequacy.ResolveBridge.resolvesModule-complete
d_resolvesModule'45'complete_2150 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Resolution.T_ResolvesModule_408
d_resolvesModule'45'complete_2150 v0 v1 ~v2 ~v3
  = du_resolvesModule'45'complete_2150 v0 v1
du_resolvesModule'45'complete_2150 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Once.Spec.Resolution.T_ResolvesModule_408
du_resolvesModule'45'complete_2150 v0 v1
  = coe
      du_go_2166 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Parser.Module.Resolve.d_resolveDecls_854
         (coe
            MAlonzo.Code.Once.Parser.Module.Resolve.d_polyDefNames_356
            (coe v1))
         (coe
            MAlonzo.Code.Once.Parser.Module.Resolve.d_collectUnaliased_130
            (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Once.Parser.Module.Resolve.d_collectAliases_80
            (coe v1))
         (coe v0) (coe v1))
-- Once.Adequacy.ResolveBridge._.go
d_go_2166 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Resolution.T_ResolvesModule_408
d_go_2166 v0 v1 ~v2 ~v3 v4 ~v5 = du_go_2166 v0 v1 v4
du_go_2166 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Spec.Resolution.T_ResolvesModule_408
du_go_2166 v0 v1 v2
  = coe
      seq (coe v2)
      (coe
         MAlonzo.Code.Once.Spec.Resolution.C_rm_418
         (coe
            du_resolvesDecls'45'complete_1854 (coe v0)
            (coe
               MAlonzo.Code.Once.Parser.Module.Resolve.d_polyDefNames_356
               (coe v1))
            (coe
               MAlonzo.Code.Once.Parser.Module.Resolve.d_collectUnaliased_130
               (coe v0) (coe v1))
            (coe
               MAlonzo.Code.Once.Parser.Module.Resolve.d_collectAliases_80
               (coe v1))
            (coe v1)))
