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
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Properties
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
-- Once.CanonicalName._≟ᶜ_
d__'8799''7580'__16 ::
  T_CanonicalName_4 ->
  T_CanonicalName_4 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799''7580'__16 v0 v1
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
d_showCanonical_40 ::
  T_CanonicalName_4 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showCanonical_40 v0
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
                               (d_showCanonical_40 (coe C_canonical_10 (coe v3)))) in
                  coe
                    (case coe v3 of
                       [] -> coe v2
                       _ -> coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
