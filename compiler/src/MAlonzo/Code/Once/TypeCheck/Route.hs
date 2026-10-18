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

module MAlonzo.Code.Once.TypeCheck.Route where

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
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Poly
import qualified MAlonzo.Code.Once.Lang.Type.Sub
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Typing
import qualified MAlonzo.Code.Once.Lang.Typing.Scope
import qualified MAlonzo.Code.Once.Spec.Name

-- Once.TypeCheck.Route.Rii
d_Rii_70 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_Rii_70
  = C_ii'45'int_160 | C_ii'45'float_170 | C_ii'45'unit_172 |
    C_ii'45'unit'45'var_174 | C_ii'45'resolved_190 | C_ii'45'own_206 |
    C_ii'45'qualified_220 | C_ii'45'local_236 | C_ii'45'import_256 |
    C_ii'45'poly'45'infer_296 | C_ii'45'annot_310 T_Rcc_82 |
    C_ii'45'pair_328 T_Rii_70 T_Rii_70 | C_ii'45'neg_338 T_Rii_70 |
    C_ii'45'neg'45'float_348 | C_ii'45'let_368 T_Rii_70 T_Rii_70 |
    C_ii'45'case_406 T_Rii_70 T_Rii_70 T_Rii_70 |
    C_ii'45'arith_430 T_Rii_70 T_Rii_70 |
    C_ii'45'farith_454 T_Rii_70 T_Rii_70 |
    C_ii'45'il_478 T_Rii_70 T_Rii_70 |
    C_ii'45'ir_502 T_Rii_70 T_Rii_70 |
    C_ii'45'cmp_526 T_Rii_70 T_Rii_70 |
    C_ii'45'id'45'app_536 T_Rii_70 | C_ii'45'fst'45'app_546 T_Rii_70 |
    C_ii'45'snd'45'app_556 T_Rii_70 |
    C_ii'45'terminal'45'app_566 T_Rii_70 | C_ii'45'apply_576 T_Rii_70 |
    C_ii'45'apply'45'eff_594 T_Rii_70 | C_ii'45'Out_612 T_Rii_70 |
    C_ii'45'Out'45'eff_638 T_Rii_70 |
    C_ii'45'app_660 T_Rii_70 T_Rcc_82 |
    C_ii'45'effApp_686 T_Rii_70 T_Rcc_82 |
    C_ii'45'app'45'spine_708 T_Ric_96 T_Rdi_138 |
    C_ii'45'spine'45'app_730 T_Ric_96 T_Rdi_138 |
    C_ii'45'spine_752 T_Rii_70 T_Rdd_156
-- Once.TypeCheck.Route.Rcc
d_Rcc_82 a0 a1 a2 a3 a4 a5 a6 = ()
data T_Rcc_82
  = C_cc'45'sub'45'l_764 T_Ric_96 | C_cc'45'sub'45'r_776 T_Ric_96 |
    C_cc'45'id_782 | C_cc'45'fst_788 | C_cc'45'snd_794 |
    C_cc'45'terminal_800 | C_cc'45'initial_806 | C_cc'45'inl_812 |
    C_cc'45'inr_818 | C_cc'45'gg_836 T_Rdd_156 T_Rcc_82 |
    C_cc'45'gf_856 T_Rdc_114 T_Ric_96 |
    C_cc'45'fg_876 T_Rdc_114 T_Ric_96 |
    C_cc'45'ff_898 T_Rii_70 T_Rcc_82 |
    C_cc'45'copair_916 T_Rcc_82 T_Rcc_82 |
    C_cc'45'fork_934 T_Rcc_82 T_Rcc_82 | C_cc'45'curry_948 T_Rcc_82 |
    C_cc'45'cata_968 T_Rcc_82 | C_cc'45'ana_988 T_Rcc_82 |
    C_cc'45'lam_1012 T_Rcc_82 |
    C_cc'45'pair'45'lit_1030 T_Rcc_82 T_Rcc_82 |
    C_cc'45'In_1046 T_Rcc_82 | C_cc'45'apply_1056 T_Rii_70 |
    C_cc'45'inl'45'app_1066 T_Rcc_82 |
    C_cc'45'inr'45'app_1076 T_Rcc_82 |
    C_cc'45'initial'45'app_1086 T_Rcc_82 | C_cc'45'poly_1122
-- Once.TypeCheck.Route.Ric
d_Ric_96 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_Ric_96
  = C_ic'45'sub_1134 T_Rii_70 | C_ic'45'pair_1152 T_Ric_96 T_Ric_96 |
    C_ic'45'apply_1162 T_Rii_70
-- Once.TypeCheck.Route.Rdc
d_Rdc_114 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_Rdc_114
  = C_dc'45'infer_1176 T_Ric_96 | C_dc'45'sub_1188 T_Rdi_138 |
    C_dc'45'lam_1210 T_Ric_96 | C_dc'45'cg_1228 T_Rdd_156 T_Rdc_114 |
    C_dc'45'cf_1248 T_Rdi_138 T_Rdc_114 | C_dc'45'id_1254 |
    C_dc'45'fst_1260 | C_dc'45'snd_1266 | C_dc'45'terminal_1272 |
    C_dc'45'initial_1278 | C_dc'45'case_1296 T_Rdc_114 T_Rdc_114 |
    C_dc'45'pair_1314 T_Rdc_114 T_Rdc_114 |
    C_dc'45'cata_1334 T_Ric_96 | C_dc'45'poly_1380
-- Once.TypeCheck.Route.Rdi
d_Rdi_138 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = ()
newtype T_Rdi_138 = C_di'45'infer_1394 T_Rii_70
-- Once.TypeCheck.Route.Rdd
d_Rdd_156 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_Rdd_156
  = C_dd'45'infer'45'l_1408 T_Rdi_138 |
    C_dd'45'infer'45'r_1422 T_Rdi_138 | C_dd'45'lam_1442 T_Rii_70 |
    C_dd'45'compose_1460 T_Rdd_156 T_Rdd_156 | C_dd'45'id_1466 |
    C_dd'45'fst_1472 | C_dd'45'snd_1478 | C_dd'45'terminal_1484 |
    C_dd'45'initial_1490 | C_dd'45'case_1508 T_Rdd_156 T_Rdd_156 |
    C_dd'45'pair_1526 T_Rdd_156 T_Rdd_156 |
    C_dd'45'cata_1546 T_Rii_70 | C_dd'45'poly_1602
