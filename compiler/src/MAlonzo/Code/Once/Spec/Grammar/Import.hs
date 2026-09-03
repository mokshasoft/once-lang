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

module MAlonzo.Code.Once.Spec.Grammar.Import where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Token

-- Once.Spec.Grammar.Import.ParsesModulePath
d_ParsesModulePath_8 a0 a1 a2 = ()
data T_ParsesModulePath_8
  = C_pmp'45'cons_18 T_ParsesModulePath_8 | C_pmp'45'dotfail_24 |
    C_pmp'45'nodot_30
-- Once.Spec.Grammar.Import.ParsesImportAlias
d_ParsesImportAlias_34 a0 a1 a2 a3 = ()
data T_ParsesImportAlias_34
  = C_pia'45'alias'45'r_42 | C_pia'45'neq'45'r_48 |
    C_pia'45'nonword'45'r_52
-- Once.Spec.Grammar.Import.ParsesImport
d_ParsesImport_54 a0 a1 a2 = ()
data T_ParsesImport_54
  = C_pi'45'mk_66 [MAlonzo.Code.Agda.Builtin.String.T_String_6]
                  [MAlonzo.Code.Once.Parser.Token.T_Token_6] T_ParsesModulePath_8
                  T_ParsesImportAlias_34
