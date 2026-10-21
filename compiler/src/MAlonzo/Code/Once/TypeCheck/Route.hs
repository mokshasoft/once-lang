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
    C_ii'45'unit'45'var_174 | C_ii'45'resolved_194 | C_ii'45'own_206 |
    C_ii'45'local_222 | C_ii'45'import_242 |
    C_ii'45'poly'45'infer_282 | C_ii'45'annot_296 T_Rcc_82 |
    C_ii'45'pair_314 T_Rii_70 T_Rii_70 | C_ii'45'neg_324 T_Rii_70 |
    C_ii'45'neg'45'float_334 | C_ii'45'let_354 T_Rii_70 T_Rii_70 |
    C_ii'45'case_404 T_Rii_70 T_Rii_70 T_Rii_70 |
    C_ii'45'arith_428 T_Rii_70 T_Rii_70 |
    C_ii'45'farith_452 T_Rii_70 T_Rii_70 |
    C_ii'45'il_476 T_Rii_70 T_Rii_70 |
    C_ii'45'ir_500 T_Rii_70 T_Rii_70 |
    C_ii'45'cmp_524 T_Rii_70 T_Rii_70 |
    C_ii'45'id'45'app_534 T_Rii_70 | C_ii'45'fst'45'app_544 T_Rii_70 |
    C_ii'45'snd'45'app_554 T_Rii_70 |
    C_ii'45'terminal'45'app_564 T_Rii_70 | C_ii'45'apply_574 T_Rii_70 |
    C_ii'45'apply'45'eff_592 T_Rii_70 | C_ii'45'Out_610 T_Rii_70 |
    C_ii'45'Out'45'eff_628 T_Rii_70 |
    C_ii'45'app_650 T_Rii_70 T_Rcc_82 |
    C_ii'45'effApp_676 T_Rii_70 T_Rcc_82 |
    C_ii'45'app'45'spine_698 T_Ric_96 T_Rdi_138 |
    C_ii'45'spine'45'app_720 T_Ric_96 T_Rdi_138 |
    C_ii'45'spine_742 T_Rii_70 T_Rdd_156
-- Once.TypeCheck.Route.Rcc
d_Rcc_82 a0 a1 a2 a3 a4 a5 a6 = ()
data T_Rcc_82
  = C_cc'45'sub'45'l_754 T_Ric_96 | C_cc'45'sub'45'r_766 T_Ric_96 |
    C_cc'45'id_772 | C_cc'45'fst_778 | C_cc'45'snd_784 |
    C_cc'45'terminal_790 | C_cc'45'initial_796 | C_cc'45'inl_802 |
    C_cc'45'inr_808 | C_cc'45'gg_826 T_Rdd_156 T_Rcc_82 |
    C_cc'45'gf_846 T_Rdc_114 T_Ric_96 |
    C_cc'45'fg_866 T_Rdc_114 T_Ric_96 |
    C_cc'45'ff_888 T_Rii_70 T_Rcc_82 |
    C_cc'45'copair_906 T_Rcc_82 T_Rcc_82 |
    C_cc'45'fork_924 T_Rcc_82 T_Rcc_82 | C_cc'45'curry_938 T_Rcc_82 |
    C_cc'45'cata_958 T_Rcc_82 | C_cc'45'ana_984 T_Rcc_82 |
    C_cc'45'loop_994 T_Rcc_82 | C_cc'45'lam_1018 T_Rcc_82 |
    C_cc'45'pair'45'lit_1036 T_Rcc_82 T_Rcc_82 |
    C_cc'45'In_1052 T_Rcc_82 | C_cc'45'apply_1062 T_Rii_70 |
    C_cc'45'inl'45'app_1072 T_Rcc_82 |
    C_cc'45'inr'45'app_1082 T_Rcc_82 |
    C_cc'45'initial'45'app_1092 T_Rcc_82 | C_cc'45'poly_1128
-- Once.TypeCheck.Route.Ric
d_Ric_96 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_Ric_96
  = C_ic'45'sub_1140 T_Rii_70 | C_ic'45'pair_1158 T_Ric_96 T_Ric_96 |
    C_ic'45'apply_1168 T_Rii_70
-- Once.TypeCheck.Route.Rdc
d_Rdc_114 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_Rdc_114
  = C_dc'45'infer_1182 T_Ric_96 | C_dc'45'sub_1194 T_Rdi_138 |
    C_dc'45'lam_1216 T_Ric_96 | C_dc'45'cg_1234 T_Rdd_156 T_Rdc_114 |
    C_dc'45'cf_1254 T_Rdi_138 T_Rdc_114 | C_dc'45'id_1260 |
    C_dc'45'fst_1266 | C_dc'45'snd_1272 | C_dc'45'terminal_1278 |
    C_dc'45'initial_1284 | C_dc'45'case_1308 T_Rdc_114 T_Rdc_114 |
    C_dc'45'pair_1326 T_Rdc_114 T_Rdc_114 |
    C_dc'45'cata_1346 T_Ric_96 | C_dc'45'poly_1392
-- Once.TypeCheck.Route.Rdi
d_Rdi_138 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = ()
newtype T_Rdi_138 = C_di'45'infer_1406 T_Rii_70
-- Once.TypeCheck.Route.Rdd
d_Rdd_156 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_Rdd_156
  = C_dd'45'infer'45'l_1420 T_Rdi_138 |
    C_dd'45'infer'45'r_1434 T_Rdi_138 | C_dd'45'lam_1454 T_Rii_70 |
    C_dd'45'compose_1472 T_Rdd_156 T_Rdd_156 | C_dd'45'id_1478 |
    C_dd'45'fst_1484 | C_dd'45'snd_1490 | C_dd'45'terminal_1496 |
    C_dd'45'initial_1502 | C_dd'45'case_1532 T_Rdd_156 T_Rdd_156 |
    C_dd'45'pair_1550 T_Rdd_156 T_Rdd_156 |
    C_dd'45'cata_1570 T_Rii_70 | C_dd'45'poly_1626
