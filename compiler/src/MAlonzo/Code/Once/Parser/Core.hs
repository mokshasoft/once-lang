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

module MAlonzo.Code.Once.Parser.Core where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Once.Parser.Token

-- Once.Parser.Core.Parser
d_Parser_6 :: () -> ()
d_Parser_6 = erased
-- Once.Parser.Core.skipNewlines
d_skipNewlines_10 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_skipNewlines_10 v0
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v0))
      (:) v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v0)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Parser.Token.C_TNewline_74
                  -> let v4 = d_skipNewlines_10 (coe v2) in
                     coe
                       (case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                            -> case coe v5 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                   -> coe
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                                              (coe v6))
                                           (coe v7))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                    (coe v2))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
