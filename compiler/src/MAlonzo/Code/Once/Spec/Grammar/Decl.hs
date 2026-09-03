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

module MAlonzo.Code.Once.Spec.Grammar.Decl where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Once.Parser.Generic.Relation
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Spec.Grammar.FunDef
import qualified MAlonzo.Code.Once.Spec.Grammar.Import
import qualified MAlonzo.Code.Once.Spec.Grammar.OpDecl
import qualified MAlonzo.Code.Once.Spec.Grammar.Signature
import qualified MAlonzo.Code.Once.Spec.Grammar.TypeAlias
import qualified MAlonzo.Code.Once.Type

-- Once.Spec.Grammar.Decl.ParsesDecl
d_ParsesDecl_8 a0 a1 a2 = ()
data T_ParsesDecl_8
  = C_pd'45'import_16 MAlonzo.Code.Once.Spec.Grammar.Import.T_ParsesImport_54 |
    C_pd'45'typealias_24 MAlonzo.Code.Once.Spec.Grammar.TypeAlias.T_ParsesTypeAliasDecl_36 |
    C_pd'45'signature_32 MAlonzo.Code.Once.Spec.Grammar.Signature.T_ParsesSignature_20 |
    C_pd'45'typesig_42 MAlonzo.Code.Once.Parser.Generic.Relation.T_ParsesTypeG_374 |
    C_pd'45'fundef_52 MAlonzo.Code.Once.Spec.Grammar.FunDef.T_ParsesFunDef_72 |
    C_pd'45'opdecl_60 MAlonzo.Code.Once.Spec.Grammar.OpDecl.T_ParsesOpDecl_56
