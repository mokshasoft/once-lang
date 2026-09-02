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

module MAlonzo.Code.Once.Spec.Resolution where

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
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.SigEffect
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.Spec.Resolution.AliasMap
d_AliasMap_6 :: ()
d_AliasMap_6 = erased
-- Once.Spec.Resolution.UnaliasedMap
d_UnaliasedMap_8 :: ()
d_UnaliasedMap_8 = erased
-- Once.Spec.Resolution.FirstAt
d_FirstAt_18 a0 a1 a2 a3 a4 = ()
data T_FirstAt_18 = C_fa'45'here_30 | C_fa'45'there_38 T_FirstAt_18
-- Once.Spec.Resolution.Absent
d_Absent_44 ::
  () ->
  () -> AgdaAny -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> ()
d_Absent_44 = erased
-- Once.Spec.Resolution.ExpandsTo
d_ExpandsTo_50 a0 a1 = ()
data T_ExpandsTo_50
  = C_ex'45'nil_52 | C_ex'45'I_56 | C_ex'45'other_62
-- Once.Spec.Resolution.ResolvesVar
d_ResolvesVar_68 a0 a1 a2 a3 = ()
data T_ResolvesVar_68
  = C_rv'45'binder_76 MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 |
    C_rv'45'gen_80 MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 |
    C_rv'45'import_88 [MAlonzo.Code.Agda.Builtin.String.T_String_6]
                      [MAlonzo.Code.Agda.Builtin.String.T_String_6] T_FirstAt_18
                      T_ExpandsTo_50 |
    C_rv'45'own_92 MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
-- Once.Spec.Resolution.ResolvesExpr
d_ResolvesExpr_98 a0 a1 a2 a3 a4 = ()
data T_ResolvesExpr_98
  = C_re'45'var_110 T_ResolvesVar_68 |
    C_re'45'qual_122 [MAlonzo.Code.Agda.Builtin.String.T_String_6]
                     [MAlonzo.Code.Agda.Builtin.String.T_String_6] T_FirstAt_18
                     T_ExpandsTo_50 |
    C_re'45'qual'45'unknown_130 MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 |
    C_re'45'res_136 |
    C_re'45'app_148 T_ResolvesExpr_98 T_ResolvesExpr_98 |
    C_re'45'lam_158 T_ResolvesExpr_98 |
    C_re'45'let_172 T_ResolvesExpr_98 T_ResolvesExpr_98 |
    C_re'45'pair_184 T_ResolvesExpr_98 T_ResolvesExpr_98 |
    C_re'45'destruct_204 T_ResolvesExpr_98 T_ResolvesExpr_98
                         T_ResolvesExpr_98 |
    C_re'45'annot_214 T_ResolvesExpr_98 |
    C_re'45'binop_228 T_ResolvesExpr_98 T_ResolvesExpr_98 |
    C_re'45'unop_238 T_ResolvesExpr_98 |
    C_re'45'ana_248 T_ResolvesExpr_98 | C_re'45'unit_252 |
    C_re'45'int_258 | C_re'45'float_270 | C_re'45'str_276
-- Once.Spec.Resolution.ResolvesDecl
d_ResolvesDecl_284 a0 a1 a2 a3 a4 = ()
data T_ResolvesDecl_284
  = C_rd'45'fundef_300 T_ResolvesExpr_98 | C_rd'45'typesig_306 |
    C_rd'45'signature_316 | C_rd'45'typealias_324 | C_rd'45'import_328
-- Once.Spec.Resolution.NotImport
d_NotImport_330 a0 = ()
data T_NotImport_330
  = C_nim'45'typesig_336 | C_nim'45'fundef_344 | C_nim'45'sig_354 |
    C_nim'45'alias_362
-- Once.Spec.Resolution.ResolvesDecls
d_ResolvesDecls_372 a0 a1 a2 a3 a4 a5 = ()
data T_ResolvesDecls_372
  = C_rds'45'nil_382 |
    C_rds'45'cons_392 T_NotImport_330 T_ResolvesDecl_284
                      T_ResolvesDecls_372 |
    C_rds'45'import_402 [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32]
                        [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] T_FirstAt_18
                        T_ResolvesDecls_372
-- Once.Spec.Resolution.ResolvesModule
d_ResolvesModule_408 a0 a1 a2 a3 = ()
newtype T_ResolvesModule_408 = C_rm_418 T_ResolvesDecls_372
