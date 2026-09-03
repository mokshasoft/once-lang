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

module MAlonzo.Code.Once.Spec.Grammar.Signature where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Once.Parser.Generic.Relation
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.SigEffect
import qualified MAlonzo.Code.Once.Type

-- Once.Spec.Grammar.Signature.ParsesEffAnnot
d_ParsesEffAnnot_8 a0 a1 a2 = ()
data T_ParsesEffAnnot_8 = C_pea'45'some_14 | C_pea'45'none_18
-- Once.Spec.Grammar.Signature.ParsesSignature
d_ParsesSignature_20 a0 a1 a2 = ()
data T_ParsesSignature_20
  = C_psig'45'mk_34 [MAlonzo.Code.Once.Parser.Token.T_Token_6]
                    MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_374
                    T_ParsesEffAnnot_8
