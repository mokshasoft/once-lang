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

module MAlonzo.Code.Once.Spec.Name where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.String.Base

-- Once.Spec.Name.CanonicalName
d_CanonicalName_6 = ()
newtype T_CanonicalName_6
  = C_canonical_12 [MAlonzo.Code.Agda.Builtin.String.T_String_6]
-- Once.Spec.Name.CanonicalName.parts
d_parts_10 ::
  T_CanonicalName_6 -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_parts_10 v0
  = case coe v0 of
      C_canonical_12 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Name.bare
d_bare_14 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> T_CanonicalName_6
d_bare_14 v0
  = coe
      C_canonical_12
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Once.Spec.Name.generatorNS
d_generatorNS_18 :: MAlonzo.Code.Agda.Builtin.String.T_String_6
d_generatorNS_18 = coe ("Generators" :: Data.Text.Text)
-- Once.Spec.Name.genWords
d_genWords_28 :: [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_genWords_28
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
-- Once.Spec.Name.GenWord
d_GenWord_30 :: MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d_GenWord_30 = erased
-- Once.Spec.Name.genNames
d_genNames_36 :: [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_genNames_36
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
-- Once.Spec.Name.NotGenerator
d_NotGenerator_38 :: T_CanonicalName_6 -> ()
d_NotGenerator_38 = erased
-- Once.Spec.Name.showCanonical
d_showCanonical_44 ::
  T_CanonicalName_6 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showCanonical_44 v0
  = case coe v0 of
      C_canonical_12 v1
        -> case coe v1 of
             [] -> coe ("" :: Data.Text.Text)
             (:) v2 v3
               -> let v4
                        = coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20
                               ("." :: Data.Text.Text)
                               (d_showCanonical_44 (coe C_canonical_12 (coe v3)))) in
                  coe
                    (case coe v3 of
                       [] -> coe v2
                       _ -> coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
