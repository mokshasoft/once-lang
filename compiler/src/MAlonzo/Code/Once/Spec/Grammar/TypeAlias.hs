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

module MAlonzo.Code.Once.Spec.Grammar.TypeAlias where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Parser.TypeRelation
import qualified MAlonzo.Code.Once.Type

-- Once.Spec.Grammar.TypeAlias.ParsesTypeAlias
d_ParsesTypeAlias_10 a0 a1 a2 a3 a4 = ()
data T_ParsesTypeAlias_10
  = C_gta'45'eq'45'r_22 MAlonzo.Code.Once.Parser.TypeRelation.T_ParsesType_106 |
    C_gta'45'word'45'r_34 T_ParsesTypeAlias_10
-- Once.Spec.Grammar.TypeAlias.ParsesTypeAliasDecl
d_ParsesTypeAliasDecl_36 a0 a1 a2 = ()
newtype T_ParsesTypeAliasDecl_36
  = C_pta'45'mk_46 T_ParsesTypeAlias_10
