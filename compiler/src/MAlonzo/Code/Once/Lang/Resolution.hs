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

module MAlonzo.Code.Once.Lang.Resolution where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Poly
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Spec.Name

-- Once.Lang.Resolution.AliasMap
d_AliasMap_6 :: ()
d_AliasMap_6 = erased
-- Once.Lang.Resolution.UnaliasedMap
d_UnaliasedMap_8 :: ()
d_UnaliasedMap_8 = erased
-- Once.Lang.Resolution.FirstAt
d_FirstAt_18 a0 a1 a2 a3 a4 = ()
data T_FirstAt_18 = C_fa'45'here_30 | C_fa'45'there_38 T_FirstAt_18
-- Once.Lang.Resolution.Absent
d_Absent_44 ::
  () ->
  () -> AgdaAny -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_Absent_44 = erased
-- Once.Lang.Resolution.ExpandsTo
d_ExpandsTo_50 a0 a1 = ()
data T_ExpandsTo_50
  = C_ex'45'nil_52 | C_ex'45'I_56 | C_ex'45'other_62
-- Once.Lang.Resolution.ResolvesVar
d_ResolvesVar_70 a0 a1 a2 a3 a4 = ()
data T_ResolvesVar_70
  = C_rv'45'binder_80 MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 |
    C_rv'45'gen_84 MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 |
    C_rv'45'import_92 [MAlonzo.Code.Agda.Builtin.String.T_String_6]
                      [MAlonzo.Code.Agda.Builtin.String.T_String_6] T_FirstAt_18
                      T_ExpandsTo_50 |
    C_rv'45'own'45'poly_96 MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
                           MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 |
    C_rv'45'own_100 MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
-- Once.Lang.Resolution.ResolvesExpr
d_ResolvesExpr_108 a0 a1 a2 a3 a4 a5 = ()
data T_ResolvesExpr_108
  = C_re'45'var_122 T_ResolvesVar_70 | C_re'45'this_128 |
    C_re'45'qual_140 [MAlonzo.Code.Agda.Builtin.String.T_String_6]
                     [MAlonzo.Code.Agda.Builtin.String.T_String_6] T_FirstAt_18
                     T_ExpandsTo_50 |
    C_re'45'qual'45'path_148 MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 |
    C_re'45'res_154 |
    C_re'45'app_166 T_ResolvesExpr_108 T_ResolvesExpr_108 |
    C_re'45'lam_176 T_ResolvesExpr_108 |
    C_re'45'let_190 T_ResolvesExpr_108 T_ResolvesExpr_108 |
    C_re'45'pair_202 T_ResolvesExpr_108 T_ResolvesExpr_108 |
    C_re'45'destruct_222 T_ResolvesExpr_108 T_ResolvesExpr_108
                         T_ResolvesExpr_108 |
    C_re'45'annot_232 T_ResolvesExpr_108 |
    C_re'45'binop_246 T_ResolvesExpr_108 T_ResolvesExpr_108 |
    C_re'45'unop_256 T_ResolvesExpr_108 |
    C_re'45'ana_266 T_ResolvesExpr_108 | C_re'45'unit_270 |
    C_re'45'int_276 | C_re'45'float_288
-- Once.Lang.Resolution.ResolvesDecl
d_ResolvesDecl_296 a0 a1 a2 a3 a4 = ()
data T_ResolvesDecl_296
  = C_rd'45'fundef_310 T_ResolvesExpr_108 AgdaAny |
    C_rd'45'typesig_316 | C_rd'45'signature_324 |
    C_rd'45'typealias_332 | C_rd'45'import_336
-- Once.Lang.Resolution.NotImport
d_NotImport_338 a0 = ()
data T_NotImport_338
  = C_nim'45'typesig_344 | C_nim'45'fundef_350 | C_nim'45'sig_358 |
    C_nim'45'alias_366
-- Once.Lang.Resolution.ResolvesDecls
d_ResolvesDecls_376 a0 a1 a2 a3 a4 a5 = ()
data T_ResolvesDecls_376
  = C_rds'45'nil_386 |
    C_rds'45'cons_396 T_NotImport_338 T_ResolvesDecl_296
                      T_ResolvesDecls_376 |
    C_rds'45'import_406 [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20]
                        [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] T_FirstAt_18
                        T_ResolvesDecls_376
-- Once.Lang.Resolution.ResolvesModule
d_ResolvesModule_412 a0 a1 a2 a3 = ()
newtype T_ResolvesModule_412 = C_rm_422 T_ResolvesDecls_376
