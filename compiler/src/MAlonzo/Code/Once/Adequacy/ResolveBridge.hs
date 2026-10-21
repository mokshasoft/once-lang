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
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Membership.DecSetoid
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Lang.Resolution
import qualified MAlonzo.Code.Once.Lang.ResolvedRefs
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Module.Resolve
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.Adequacy.ResolveBridge._._∈?_
d__'8712''63'__8 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8712''63'__8
  = let v0 = MAlonzo.Code.Data.String.Properties.d__'8799'__54 in
    coe
      (coe
         MAlonzo.Code.Data.List.Membership.DecSetoid.du__'8712''63'__60
         (coe
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
            (coe v0)))
-- Once.Adequacy.ResolveBridge.lookupUn-complete
d_lookupUn'45'complete_16 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Lang.Resolution.T_FirstAt_18 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookupUn'45'complete_16 = erased
-- Once.Adequacy.ResolveBridge.lookupUn-absent
d_lookupUn'45'absent_104 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookupUn'45'absent_104 = erased
-- Once.Adequacy.ResolveBridge.lookupUn-sound
d_lookupUn'45'sound_154 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Resolution.T_FirstAt_18
d_lookupUn'45'sound_154 v0 v1 ~v2 ~v3
  = du_lookupUn'45'sound_154 v0 v1
du_lookupUn'45'sound_154 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Resolution.T_FirstAt_18
du_lookupUn'45'sound_154 v0 v1
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
                                     (coe MAlonzo.Code.Once.Lang.Resolution.C_fa'45'here_30)
                              else coe
                                     seq (coe v8)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Resolution.C_fa'45'there_38
                                        (coe du_lookupUn'45'sound_154 (coe v3) (coe v1)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ResolveBridge.lookupUn-nothing
d_lookupUn'45'nothing_200 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_lookupUn'45'nothing_200 v0 v1 ~v2
  = du_lookupUn'45'nothing_200 v0 v1
du_lookupUn'45'nothing_200 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_lookupUn'45'nothing_200 v0 v1
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
                                    (coe du_lookupUn'45'nothing_200 (coe v3) (coe v1))))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ResolveBridge.lookupAl-complete
d_lookupAl'45'complete_246 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Lang.Resolution.T_FirstAt_18 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookupAl'45'complete_246 = erased
-- Once.Adequacy.ResolveBridge.lookupAl-absent
d_lookupAl'45'absent_336 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookupAl'45'absent_336 = erased
-- Once.Adequacy.ResolveBridge.lookupAl-sound
d_lookupAl'45'sound_388 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Resolution.T_FirstAt_18
d_lookupAl'45'sound_388 v0 v1 ~v2 ~v3
  = du_lookupAl'45'sound_388 v0 v1
du_lookupAl'45'sound_388 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Resolution.T_FirstAt_18
du_lookupAl'45'sound_388 v0 v1
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
                                     (coe MAlonzo.Code.Once.Lang.Resolution.C_fa'45'here_30)
                              else coe
                                     seq (coe v8)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Resolution.C_fa'45'there_38
                                        (coe du_lookupAl'45'sound_388 (coe v3) (coe v1)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ResolveBridge.lookupAl-nothing
d_lookupAl'45'nothing_430 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_lookupAl'45'nothing_430 v0 v1 ~v2
  = du_lookupAl'45'nothing_430 v0 v1
du_lookupAl'45'nothing_430 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_lookupAl'45'nothing_430 v0 v1
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
                                    (coe du_lookupAl'45'nothing_430 (coe v3) (coe v1))))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ResolveBridge.expandPath-complete
d_expandPath'45'complete_472 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Lang.Resolution.T_ExpandsTo_50 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_expandPath'45'complete_472 = erased
-- Once.Adequacy.ResolveBridge.expandPath-sound
d_expandPath'45'sound_512 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Lang.Resolution.T_ExpandsTo_50
d_expandPath'45'sound_512 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Once.Lang.Resolution.C_ex'45'nil_52
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
                              seq (coe v5) (coe MAlonzo.Code.Once.Lang.Resolution.C_ex'45'I_56)
                       else coe
                              seq (coe v5)
                              (coe MAlonzo.Code.Once.Lang.Resolution.C_ex'45'other_62)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ResolveBridge.GenWord-isBuiltinName
d_GenWord'45'isBuiltinName_534 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_GenWord'45'isBuiltinName_534 = erased
-- Once.Adequacy.ResolveBridge.resolvesVar-sound
d_resolvesVar'45'sound_564 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Resolution.T_ResolvesVar_70 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolvesVar'45'sound_564 = erased
-- Once.Adequacy.ResolveBridge.resolvesVar-complete
d_resolvesVar'45'complete_704 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Resolution.T_ResolvesVar_70
d_resolvesVar'45'complete_704 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
              (coe
                 MAlonzo.Code.Data.List.Relation.Unary.Any.du_any'63'_138
                 (coe MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v3))
                 (coe v1)) in
    coe
      (if coe v4
         then coe
                MAlonzo.Code.Once.Lang.Resolution.C_rv'45'binder_80
                (coe
                   MAlonzo.Code.Relation.Nullary.Reflects.du_invert_38
                   (coe
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_proof_30
                      (coe
                         MAlonzo.Code.Data.List.Membership.DecSetoid.du__'8712''63'__60
                         (coe
                            MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
                            (coe MAlonzo.Code.Data.String.Properties.d__'8799'__54))
                         (coe v3) (coe v1))))
         else (let v5
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
                                  (\ v5 ->
                                     coe
                                       MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                       (coe v3))
                                  (coe
                                     MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                                     (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                                     (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v3)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                        ("id" :: Data.Text.Text))))
                               (coe
                                  MAlonzo.Code.Data.List.Relation.Unary.Any.du_any'63'_138
                                  (coe
                                     (\ v5 ->
                                        coe
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                          erased
                                          (\ v6 ->
                                             coe
                                               MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                               (coe v3))
                                          (coe
                                             MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                             (coe v3) (coe v5))))
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
                 (if coe v5
                    then coe
                           MAlonzo.Code.Once.Lang.Resolution.C_rv'45'gen_84
                           (coe
                              MAlonzo.Code.Once.Parser.Module.Resolve.du_isBuiltinName'45'sound_202
                              (coe v3))
                    else (let v6
                                = MAlonzo.Code.Once.Parser.Module.Resolve.d_lookupUnaliased_166
                                    (coe v2) (coe v3) in
                          coe
                            (case coe v6 of
                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                                 -> coe
                                      MAlonzo.Code.Once.Lang.Resolution.C_rv'45'import_92 v7
                                      (MAlonzo.Code.Once.Parser.Module.Resolve.d_expandPath_324
                                         (coe v7))
                                      (coe du_lookupUn'45'sound_154 (coe v2) (coe v3))
                                      (d_expandPath'45'sound_512 (coe v7))
                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                 -> let v7
                                          = MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                              (coe
                                                 MAlonzo.Code.Data.List.Relation.Unary.Any.du_any'63'_138
                                                 (coe
                                                    MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                                    (coe v3))
                                                 (coe v0)) in
                                    coe
                                      (if coe v7
                                         then coe
                                                MAlonzo.Code.Once.Lang.Resolution.C_rv'45'own'45'poly_96
                                                (coe du_lookupUn'45'nothing_200 (coe v2) (coe v3))
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Reflects.du_invert_38
                                                   (coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_proof_30
                                                      (coe
                                                         MAlonzo.Code.Data.List.Membership.DecSetoid.du__'8712''63'__60
                                                         (coe
                                                            MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
                                                            (coe
                                                               MAlonzo.Code.Data.String.Properties.d__'8799'__54))
                                                         (coe v3) (coe v0))))
                                         else coe
                                                MAlonzo.Code.Once.Lang.Resolution.C_rv'45'own_100
                                                (coe du_lookupUn'45'nothing_200 (coe v2) (coe v3)))
                               _ -> MAlonzo.RTE.mazUnreachableError)))))
-- Once.Adequacy.ResolveBridge.resolves-sound
d_resolves'45'sound_816 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Resolution.T_ResolvesExpr_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolves'45'sound_816 = erased
-- Once.Adequacy.ResolveBridge._.cong₃
d_cong'8323'_1080 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Resolution.T_ResolvesExpr_108 ->
  MAlonzo.Code.Once.Lang.Resolution.T_ResolvesExpr_108 ->
  MAlonzo.Code.Once.Lang.Resolution.T_ResolvesExpr_108 ->
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
d_cong'8323'_1080 = erased
-- Once.Adequacy.ResolveBridge.resolves-complete
d_resolves'45'complete_1176 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Resolution.T_ResolvesExpr_108
d_resolves'45'complete_1176 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.Lang.Syntax.C_RVar_36 v5
        -> coe
             MAlonzo.Code.Once.Lang.Resolution.C_re'45'var_122
             (d_resolvesVar'45'complete_704 (coe v0) (coe v3) (coe v1) (coe v5))
      MAlonzo.Code.Once.Lang.Syntax.C_RQualified_38 v5 v6
        -> let v7
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     erased
                     (\ v7 ->
                        coe
                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                          (coe v6))
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v6)
                        (coe ("this" :: Data.Text.Text))) in
           coe
             (case coe v7 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                  -> if coe v8
                       then coe
                              seq (coe v9)
                              (coe MAlonzo.Code.Once.Lang.Resolution.C_re'45'this_128)
                       else coe
                              seq (coe v9)
                              (let v10
                                     = MAlonzo.Code.Once.Parser.Module.Resolve.d_lookupImportAlias_94
                                         (coe v2) (coe v6) in
                               coe
                                 (case coe v10 of
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                      -> coe
                                           MAlonzo.Code.Once.Lang.Resolution.C_re'45'qual_140 v11
                                           (MAlonzo.Code.Once.Parser.Module.Resolve.d_expandPath_324
                                              (coe v11))
                                           (coe du_lookupAl'45'sound_388 (coe v2) (coe v6))
                                           (d_expandPath'45'sound_512 (coe v11))
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                      -> coe
                                           MAlonzo.Code.Once.Lang.Resolution.C_re'45'qual'45'path_148
                                           (coe du_lookupAl'45'nothing_430 (coe v2) (coe v6))
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40 v5
        -> coe MAlonzo.Code.Once.Lang.Resolution.C_re'45'res_154
      MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v5 v6
        -> coe
             MAlonzo.Code.Once.Lang.Resolution.C_re'45'app_166
             (d_resolves'45'complete_1176
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v5))
             (d_resolves'45'complete_1176
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v6))
      MAlonzo.Code.Once.Lang.Syntax.C_RLam_44 v5 v6
        -> coe
             MAlonzo.Code.Once.Lang.Resolution.C_re'45'lam_176
             (d_resolves'45'complete_1176
                (coe v0) (coe v1) (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5) (coe v3))
                (coe v6))
      MAlonzo.Code.Once.Lang.Syntax.C_RLet_46 v5 v6 v7
        -> coe
             MAlonzo.Code.Once.Lang.Resolution.C_re'45'let_190
             (d_resolves'45'complete_1176
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v6))
             (d_resolves'45'complete_1176
                (coe v0) (coe v1) (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5) (coe v3))
                (coe v7))
      MAlonzo.Code.Once.Lang.Syntax.C_RPair_48 v5 v6
        -> coe
             MAlonzo.Code.Once.Lang.Resolution.C_re'45'pair_202
             (d_resolves'45'complete_1176
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v5))
             (d_resolves'45'complete_1176
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v6))
      MAlonzo.Code.Once.Lang.Syntax.C_RDestruct_50 v5 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.Lang.Resolution.C_re'45'destruct_222
             (d_resolves'45'complete_1176
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v5))
             (d_resolves'45'complete_1176
                (coe v0) (coe v1) (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v6) (coe v3))
                (coe v7))
             (d_resolves'45'complete_1176
                (coe v0) (coe v1) (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v8) (coe v3))
                (coe v9))
      MAlonzo.Code.Once.Lang.Syntax.C_RUnit_52
        -> coe MAlonzo.Code.Once.Lang.Resolution.C_re'45'unit_270
      MAlonzo.Code.Once.Lang.Syntax.C_RInt_54 v5
        -> coe MAlonzo.Code.Once.Lang.Resolution.C_re'45'int_276
      MAlonzo.Code.Once.Lang.Syntax.C_RFloat_56 v5 v6 v7 v8
        -> coe MAlonzo.Code.Once.Lang.Resolution.C_re'45'float_288
      MAlonzo.Code.Once.Lang.Syntax.C_RAnnot_58 v5 v6
        -> coe
             MAlonzo.Code.Once.Lang.Resolution.C_re'45'annot_232
             (d_resolves'45'complete_1176
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v5))
      MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_60 v5 v6 v7
        -> coe
             MAlonzo.Code.Once.Lang.Resolution.C_re'45'binop_246
             (d_resolves'45'complete_1176
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v6))
             (d_resolves'45'complete_1176
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v7))
      MAlonzo.Code.Once.Lang.Syntax.C_RUnaryOp_62 v6
        -> coe
             MAlonzo.Code.Once.Lang.Resolution.C_re'45'unop_256
             (d_resolves'45'complete_1176
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v6))
      MAlonzo.Code.Once.Lang.Syntax.C_RAna_64 v5 v6
        -> coe
             MAlonzo.Code.Once.Lang.Resolution.C_re'45'ana_266
             (d_resolves'45'complete_1176
                (coe v0) (coe v1) (coe v2) (coe v3) (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ResolveBridge.resolvesDecl-sound
d_resolvesDecl'45'sound_1438 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20 ->
  MAlonzo.Code.Once.Lang.Resolution.T_ResolvesDecl_296 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolvesDecl'45'sound_1438 = erased
-- Once.Adequacy.ResolveBridge.DeclGood
d_DeclGood_1474 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20 -> ()
d_DeclGood_1474 = erased
-- Once.Adequacy.ResolveBridge.resolvesDecl-complete
d_resolvesDecl'45'complete_1490 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Resolution.T_ResolvesDecl_296
d_resolvesDecl'45'complete_1490 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_22 v5 v6
        -> coe MAlonzo.Code.Once.Lang.Resolution.C_rd'45'typesig_316
      MAlonzo.Code.Once.Parser.Module.Core.C_DFunDef_24 v5 v6
        -> coe
             MAlonzo.Code.Once.Lang.Resolution.C_rd'45'fundef_310
             (d_resolves'45'complete_1176
                (coe v0) (coe v1) (coe v2)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v6))
             v4
      MAlonzo.Code.Once.Parser.Module.Core.C_DSignature_26 v5 v6 v7
        -> coe MAlonzo.Code.Once.Lang.Resolution.C_rd'45'signature_324
      MAlonzo.Code.Once.Parser.Module.Core.C_DTypeAlias_28 v5 v6 v7
        -> coe MAlonzo.Code.Once.Lang.Resolution.C_rd'45'typealias_332
      MAlonzo.Code.Once.Parser.Module.Core.C_DImport_30 v5
        -> coe MAlonzo.Code.Once.Lang.Resolution.C_rd'45'import_336
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ResolveBridge.consDecl-ok
d_consDecl'45'ok_1558 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20 ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  MAlonzo.Code.Once.Lang.Resolution.T_ResolvesDecl_296 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_consDecl'45'ok_1558 = erased
-- Once.Adequacy.ResolveBridge._.at
d_at_1578 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Resolution.T_ResolvesExpr_108 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_at_1578 = erased
-- Once.Adequacy.ResolveBridge.consDecl-inv
d_consDecl'45'inv_1606 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_consDecl'45'inv_1606 v0 v1 ~v2 ~v3 ~v4
  = du_consDecl'45'inv_1606 v0 v1
du_consDecl'45'inv_1606 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_consDecl'45'inv_1606 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_22 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Parser.Module.Core.C_DFunDef_24 v2 v3
        -> coe
             du_at_1626
             (coe
                MAlonzo.Code.Once.Lang.ResolvedRefs.d_goodRefs'63'_200 (coe v0)
                (coe v3))
      MAlonzo.Code.Once.Parser.Module.Core.C_DSignature_26 v2 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Parser.Module.Core.C_DTypeAlias_28 v2 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Parser.Module.Core.C_DImport_30 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ResolveBridge._.at
d_at_1626 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_at_1626 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 = du_at_1626 v6
du_at_1626 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_at_1626 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v1 v2
        -> coe
             seq (coe v1)
             (case coe v2 of
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v3
                  -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v3)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ResolveBridge.path≟-refl
d_path'8799''45'refl_1666 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_path'8799''45'refl_1666 = erased
-- Once.Adequacy.ResolveBridge.path≟-sound
d_path'8799''45'sound_1690 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_path'8799''45'sound_1690 = erased
-- Once.Adequacy.ResolveBridge.lookupMod-complete
d_lookupMod'45'complete_1732 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Lang.Resolution.T_FirstAt_18 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookupMod'45'complete_1732 = erased
-- Once.Adequacy.ResolveBridge.import-red
d_import'45'red_1812 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Import_8 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_import'45'red_1812 = erased
-- Once.Adequacy.ResolveBridge._.go
d_go_1846 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Import_8 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go_1846 = erased
-- Once.Adequacy.ResolveBridge.resolvesDecls-sound
d_resolvesDecls'45'sound_1880 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  MAlonzo.Code.Once.Lang.Resolution.T_ResolvesDecls_376 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolvesDecls'45'sound_1880 = erased
-- Once.Adequacy.ResolveBridge.resolvesModule-sound
d_resolvesModule'45'sound_1996 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Once.Lang.Resolution.T_ResolvesModule_412 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolvesModule'45'sound_1996 = erased
-- Once.Adequacy.ResolveBridge.path≟-false⇒≢
d_path'8799''45'false'8658''8802'_2012 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_path'8799''45'false'8658''8802'_2012 = erased
-- Once.Adequacy.ResolveBridge.lookupMod-sound
d_lookupMod'45'sound_2032 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Resolution.T_FirstAt_18
d_lookupMod'45'sound_2032 v0 v1 ~v2 ~v3
  = du_lookupMod'45'sound_2032 v0 v1
du_lookupMod'45'sound_2032 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Once.Lang.Resolution.T_FirstAt_18
du_lookupMod'45'sound_2032 v0 v1
  = case coe v0 of
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> let v6
                        = MAlonzo.Code.Once.Parser.Module.Resolve.d__path'8799'__14
                            (coe v4) (coe v1) in
                  coe
                    (if coe v6
                       then coe MAlonzo.Code.Once.Lang.Resolution.C_fa'45'here_30
                       else coe
                              MAlonzo.Code.Once.Lang.Resolution.C_fa'45'there_38
                              (coe du_lookupMod'45'sound_2032 (coe v3) (coe v1)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ResolveBridge.resolvesDecls-complete
d_resolvesDecls'45'complete_2088 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Resolution.T_ResolvesDecls_376
d_resolvesDecls'45'complete_2088 v0 v1 v2 v3 v4 ~v5 ~v6
  = du_resolvesDecls'45'complete_2088 v0 v1 v2 v3 v4
du_resolvesDecls'45'complete_2088 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  MAlonzo.Code.Once.Lang.Resolution.T_ResolvesDecls_376
du_resolvesDecls'45'complete_2088 v0 v1 v2 v3 v4
  = case coe v4 of
      [] -> coe MAlonzo.Code.Once.Lang.Resolution.C_rds'45'nil_386
      (:) v5 v6
        -> case coe v5 of
             MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_22 v7 v8
               -> coe
                    du_rdc'45'cons_2132 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
                    (coe MAlonzo.Code.Once.Lang.Resolution.C_nim'45'typesig_344)
                    (coe v6)
                    (coe
                       MAlonzo.Code.Once.Parser.Module.Resolve.d_resolveDecls_954 (coe v1)
                       (coe v2) (coe v3) (coe v0) (coe v6))
             MAlonzo.Code.Once.Parser.Module.Core.C_DFunDef_24 v7 v8
               -> coe
                    du_rdc'45'cons_2132 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
                    (coe MAlonzo.Code.Once.Lang.Resolution.C_nim'45'fundef_350)
                    (coe v6)
                    (coe
                       MAlonzo.Code.Once.Parser.Module.Resolve.d_resolveDecls_954 (coe v1)
                       (coe v2) (coe v3) (coe v0) (coe v6))
             MAlonzo.Code.Once.Parser.Module.Core.C_DSignature_26 v7 v8 v9
               -> coe
                    du_rdc'45'cons_2132 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
                    (coe MAlonzo.Code.Once.Lang.Resolution.C_nim'45'sig_358) (coe v6)
                    (coe
                       MAlonzo.Code.Once.Parser.Module.Resolve.d_resolveDecls_954 (coe v1)
                       (coe v2) (coe v3) (coe v0) (coe v6))
             MAlonzo.Code.Once.Parser.Module.Core.C_DTypeAlias_28 v7 v8 v9
               -> coe
                    du_rdc'45'cons_2132 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)
                    (coe MAlonzo.Code.Once.Lang.Resolution.C_nim'45'alias_366) (coe v6)
                    (coe
                       MAlonzo.Code.Once.Parser.Module.Resolve.d_resolveDecls_954 (coe v1)
                       (coe v2) (coe v3) (coe v0) (coe v6))
             MAlonzo.Code.Once.Parser.Module.Core.C_DImport_30 v7
               -> coe
                    du_rdc'45'import_2112 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7)
                    (coe v6)
                    (coe
                       MAlonzo.Code.Once.Parser.Module.Resolve.d_lookupModule_44 (coe v0)
                       (coe MAlonzo.Code.Once.Parser.Module.Core.d_path_14 (coe v7)))
                    (coe
                       MAlonzo.Code.Once.Parser.Module.Resolve.d_resolveDecls_954 (coe v1)
                       (coe v2) (coe v3) (coe v0) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ResolveBridge.rdc-import
d_rdc'45'import_2112 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Import_8 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Resolution.T_ResolvesDecls_376
d_rdc'45'import_2112 v0 v1 v2 v3 v4 v5 ~v6 v7 ~v8 v9 ~v10 ~v11
  = du_rdc'45'import_2112 v0 v1 v2 v3 v4 v5 v7 v9
du_rdc'45'import_2112 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Import_8 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Lang.Resolution.T_ResolvesDecls_376
du_rdc'45'import_2112 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
        -> case coe v8 of
             MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_38 v9
               -> case coe v7 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v10
                      -> coe
                           MAlonzo.Code.Once.Lang.Resolution.C_rds'45'import_406 v9 v10
                           (coe
                              du_lookupMod'45'sound_2032 (coe v0)
                              (coe MAlonzo.Code.Once.Parser.Module.Core.d_path_14 (coe v4)))
                           (coe
                              du_resolvesDecls'45'complete_2088 (coe v0) (coe v1) (coe v2)
                              (coe v3) (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ResolveBridge.rdc-cons
d_rdc'45'cons_2132 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20 ->
  MAlonzo.Code.Once.Lang.Resolution.T_NotImport_338 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Resolution.T_ResolvesDecls_376
d_rdc'45'cons_2132 v0 v1 v2 v3 v4 v5 v6 ~v7 v8 ~v9 ~v10
  = du_rdc'45'cons_2132 v0 v1 v2 v3 v4 v5 v6 v8
du_rdc'45'cons_2132 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20 ->
  MAlonzo.Code.Once.Lang.Resolution.T_NotImport_338 ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Lang.Resolution.T_ResolvesDecls_376
du_rdc'45'cons_2132 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
        -> coe
             MAlonzo.Code.Once.Lang.Resolution.C_rds'45'cons_396 v5
             (d_resolvesDecl'45'complete_1490
                (coe v1) (coe v2) (coe v3) (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                   (coe
                      du_consDecl'45'inv_1606 (coe v1)
                      (coe
                         MAlonzo.Code.Once.Parser.Module.Resolve.d_canonDecl_914 (coe v1)
                         (coe v2) (coe v3) (coe v4)))))
             (coe
                du_resolvesDecls'45'complete_2088 (coe v0) (coe v1) (coe v2)
                (coe v3) (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.ResolveBridge.resolveImports-ok
d_resolveImports'45'ok_2348 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveImports'45'ok_2348 = erased
-- Once.Adequacy.ResolveBridge.resolveImports-bad
d_resolveImports'45'bad_2368 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_resolveImports'45'bad_2368 = erased
-- Once.Adequacy.ResolveBridge.resolvesModule-complete
d_resolvesModule'45'complete_2388 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Resolution.T_ResolvesModule_412
d_resolvesModule'45'complete_2388 v0 v1 ~v2 ~v3
  = du_resolvesModule'45'complete_2388 v0 v1
du_resolvesModule'45'complete_2388 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  MAlonzo.Code.Once.Lang.Resolution.T_ResolvesModule_412
du_resolvesModule'45'complete_2388 v0 v1
  = coe
      du_go_2404 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Once.Parser.Module.Resolve.d_resolveDecls_954
         (coe
            MAlonzo.Code.Once.Parser.Module.Resolve.d_polyDefNames_320
            (coe v1))
         (coe
            MAlonzo.Code.Once.Parser.Module.Resolve.d_collectUnaliased_134
            (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Once.Parser.Module.Resolve.d_collectAliases_84
            (coe v1))
         (coe v0) (coe v1))
-- Once.Adequacy.ResolveBridge._.go
d_go_2404 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Lang.Resolution.T_ResolvesModule_412
d_go_2404 v0 v1 ~v2 ~v3 v4 ~v5 = du_go_2404 v0 v1 v4
du_go_2404 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Once.Lang.Resolution.T_ResolvesModule_412
du_go_2404 v0 v1 v2
  = coe
      seq (coe v2)
      (coe
         MAlonzo.Code.Once.Lang.Resolution.C_rm_422
         (coe
            du_resolvesDecls'45'complete_2088 (coe v0)
            (coe
               MAlonzo.Code.Once.Parser.Module.Resolve.d_polyDefNames_320
               (coe v1))
            (coe
               MAlonzo.Code.Once.Parser.Module.Resolve.d_collectUnaliased_134
               (coe v0) (coe v1))
            (coe
               MAlonzo.Code.Once.Parser.Module.Resolve.d_collectAliases_84
               (coe v1))
            (coe v1)))
