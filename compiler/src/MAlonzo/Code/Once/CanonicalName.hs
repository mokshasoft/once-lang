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

module MAlonzo.Code.Once.CanonicalName where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.CanonicalName.CanonicalName
d_CanonicalName_4 = ()
newtype T_CanonicalName_4
  = C_canonical_10 [MAlonzo.Code.Agda.Builtin.String.T_String_6]
-- Once.CanonicalName.CanonicalName.parts
d_parts_8 ::
  T_CanonicalName_4 -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_parts_8 v0
  = case coe v0 of
      C_canonical_10 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CanonicalName.bare
d_bare_12 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_CanonicalName_4
d_bare_12 v0
  = coe
      C_canonical_10
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Once.CanonicalName.generatorNS
d_generatorNS_16 :: MAlonzo.Code.Agda.Builtin.String.T_String_6
d_generatorNS_16 = coe ("Generators" :: Data.Text.Text)
-- Once.CanonicalName.gen≢bare
d_gen'8802'bare_26 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_gen'8802'bare_26 = erased
-- Once.CanonicalName.gen-inj
d_gen'45'inj_36 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_gen'45'inj_36 = erased
-- Once.CanonicalName.genWords
d_genWords_38 :: [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_genWords_38
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe ("id" :: Data.Text.Text))
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
                                       (coe ("compose" :: Data.Text.Text))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe ("case" :: Data.Text.Text))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe ("cata" :: Data.Text.Text))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe ("ana" :: Data.Text.Text))
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe ("In" :: Data.Text.Text))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe ("Out" :: Data.Text.Text))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))))))
-- Once.CanonicalName.GenWord
d_GenWord_40 :: MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d_GenWord_40 = erased
-- Once.CanonicalName.genWord?
d_genWord'63'_48 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_genWord'63'_48 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.Any.du_any'63'_138
      (coe MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0))
      (coe d_genWords_38)
-- Once.CanonicalName.genWord?-no
d_genWord'63''45'no_58 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_genWord'63''45'no_58 v0 ~v1 = du_genWord'63''45'no_58 v0
du_genWord'63''45'no_58 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_genWord'63''45'no_58 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              (coe MAlonzo.Code.Data.List.Relation.Unary.Any.du_fromSum_132)
              (coe MAlonzo.Code.Data.List.Relation.Unary.Any.du_toSum_126)
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'8846''45'dec__96
                 (coe
                    MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
                    (coe ("id" :: Data.Text.Text)))
                 (coe
                    MAlonzo.Code.Data.List.Relation.Unary.Any.du_any'63'_138
                    (coe MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0))
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
                                                     (coe ("compose" :: Data.Text.Text))
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                        (coe ("case" :: Data.Text.Text))
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                           (coe ("cata" :: Data.Text.Text))
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe ("ana" :: Data.Text.Text))
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                 (coe ("In" :: Data.Text.Text))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                    (coe ("Out" :: Data.Text.Text))
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))) in
    coe
      (case coe v1 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
           -> if coe v2
                then coe
                       seq (coe v3) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                else coe
                       seq (coe v3)
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.CanonicalName.genNames
d_genNames_80 :: [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_genNames_80
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe ("id" :: Data.Text.Text))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe ("fst" :: Data.Text.Text))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe ("snd" :: Data.Text.Text))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe ("terminal" :: Data.Text.Text))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe ("initial" :: Data.Text.Text))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe ("inl" :: Data.Text.Text))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe ("inr" :: Data.Text.Text))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe ("unit" :: Data.Text.Text))
                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))
-- Once.CanonicalName.NotGenerator
d_NotGenerator_82 :: T_CanonicalName_4 -> ()
d_NotGenerator_82 = erased
-- Once.CanonicalName.bare-NotGenerator
d_bare'45'NotGenerator_90 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_bare'45'NotGenerator_90 ~v0 = du_bare'45'NotGenerator_90
du_bare'45'NotGenerator_90 ::
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_bare'45'NotGenerator_90
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))
-- Once.CanonicalName._≟ᶜ_
d__'8799''7580'__110 ::
  T_CanonicalName_4 ->
  T_CanonicalName_4 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799''7580'__110 v0 v1
  = case coe v0 of
      C_canonical_10 v2
        -> case coe v1 of
             C_canonical_10 v3
               -> let v4
                        = coe
                            MAlonzo.Code.Data.List.Properties.du_'8801''45'dec_60
                            (coe MAlonzo.Code.Data.String.Properties.d__'8799'__54) (coe v2)
                            (coe v3) in
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
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.CanonicalName.showCanonical
d_showCanonical_134 ::
  T_CanonicalName_4 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showCanonical_134 v0
  = case coe v0 of
      C_canonical_10 v1
        -> case coe v1 of
             [] -> coe ("" :: Data.Text.Text)
             (:) v2 v3
               -> let v4
                        = coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("." :: Data.Text.Text)
                               (d_showCanonical_134 (coe C_canonical_10 (coe v3)))) in
                  coe
                    (case coe v3 of
                       [] -> coe v2
                       _ -> coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
