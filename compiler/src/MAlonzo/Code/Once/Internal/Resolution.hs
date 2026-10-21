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

module MAlonzo.Code.Once.Internal.Resolution where

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
import qualified MAlonzo.Code.Once.Internal.Syntax
import qualified MAlonzo.Code.Once.Internal.Type
import qualified MAlonzo.Code.Once.Internal.Type.Poly
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Spec.Name

-- Once.Internal.Resolution.AliasMap
d_AliasMap_6 :: ()
d_AliasMap_6 = erased
-- Once.Internal.Resolution.UnaliasedMap
d_UnaliasedMap_8 :: ()
d_UnaliasedMap_8 = erased
-- Once.Internal.Resolution.FirstAt
d_FirstAt_18 a0 a1 a2 a3 a4 = ()
data T_FirstAt_18 = C_fa'45'here_30 | C_fa'45'there_38 T_FirstAt_18
-- Once.Internal.Resolution.Absent
d_Absent_44 ::
  () ->
  () -> AgdaAny -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_Absent_44 = erased
-- Once.Internal.Resolution.ExpandsTo
d_ExpandsTo_50 a0 a1 = ()
data T_ExpandsTo_50
  = C_ex'45'nil_52 | C_ex'45'I_56 | C_ex'45'other_62
-- Once.Internal.Resolution.ResolvesVar
d_ResolvesVar_68 a0 a1 a2 a3 = ()
data T_ResolvesVar_68
  = C_rv'45'binder_76 MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 |
    C_rv'45'gen_80 MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 |
    C_rv'45'import_88 [MAlonzo.Code.Agda.Builtin.String.T_String_6]
                      [MAlonzo.Code.Agda.Builtin.String.T_String_6] T_FirstAt_18
                      T_ExpandsTo_50 |
    C_rv'45'own_92 MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
-- Once.Internal.Resolution.ResolvesExpr
d_ResolvesExpr_98 a0 a1 a2 a3 a4 = ()
data T_ResolvesExpr_98
  = C_re'45'var_110 T_ResolvesVar_68 | C_re'45'this_116 |
    C_re'45'qual_128 [MAlonzo.Code.Agda.Builtin.String.T_String_6]
                     [MAlonzo.Code.Agda.Builtin.String.T_String_6] T_FirstAt_18
                     T_ExpandsTo_50 |
    C_re'45'qual'45'path_136 MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 |
    C_re'45'res_142 |
    C_re'45'app_154 T_ResolvesExpr_98 T_ResolvesExpr_98 |
    C_re'45'lam_164 T_ResolvesExpr_98 |
    C_re'45'let_178 T_ResolvesExpr_98 T_ResolvesExpr_98 |
    C_re'45'pair_190 T_ResolvesExpr_98 T_ResolvesExpr_98 |
    C_re'45'destruct_210 T_ResolvesExpr_98 T_ResolvesExpr_98
                         T_ResolvesExpr_98 |
    C_re'45'annot_220 T_ResolvesExpr_98 |
    C_re'45'binop_234 T_ResolvesExpr_98 T_ResolvesExpr_98 |
    C_re'45'unop_244 T_ResolvesExpr_98 |
    C_re'45'ana_254 T_ResolvesExpr_98 | C_re'45'unit_258 |
    C_re'45'int_264 | C_re'45'float_276
-- Once.Internal.Resolution.ResolvesDecl
d_ResolvesDecl_282 a0 a1 a2 a3 = ()
data T_ResolvesDecl_282
  = C_rd'45'fundef_294 T_ResolvesExpr_98 AgdaAny |
    C_rd'45'typesig_300 | C_rd'45'signature_308 |
    C_rd'45'typealias_316 | C_rd'45'import_320
-- Once.Internal.Resolution.NotImport
d_NotImport_322 a0 = ()
data T_NotImport_322
  = C_nim'45'typesig_328 | C_nim'45'fundef_334 | C_nim'45'sig_342 |
    C_nim'45'alias_350
-- Once.Internal.Resolution.ResolvesDecls
d_ResolvesDecls_358 a0 a1 a2 a3 a4 = ()
data T_ResolvesDecls_358
  = C_rds'45'nil_366 |
    C_rds'45'cons_376 T_NotImport_322 T_ResolvesDecl_282
                      T_ResolvesDecls_358 |
    C_rds'45'import_386 [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20]
                        [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_20] T_FirstAt_18
                        T_ResolvesDecls_358
-- Once.Internal.Resolution.ResolvesModule
d_ResolvesModule_390 a0 a1 a2 = ()
newtype T_ResolvesModule_390 = C_rm_398 T_ResolvesDecls_358
