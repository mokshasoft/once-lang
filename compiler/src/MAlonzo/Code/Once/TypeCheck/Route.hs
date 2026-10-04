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
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Rigid
import qualified MAlonzo.Code.Once.Type.Sub
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.TypeCheck.Route.Rii
d_Rii_70 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_Rii_70
  = C_ii'45'int_160 | C_ii'45'float_170 | C_ii'45'unit_172 |
    C_ii'45'unit'45'var_174 | C_ii'45'resolved_190 |
    C_ii'45'qualified_204 | C_ii'45'local_220 | C_ii'45'import_240 |
    C_ii'45'poly'45'infer_280 | C_ii'45'annot_294 T_Rcc_82 |
    C_ii'45'pair_312 T_Rii_70 T_Rii_70 | C_ii'45'neg_322 T_Rii_70 |
    C_ii'45'neg'45'float_332 | C_ii'45'let_352 T_Rii_70 T_Rii_70 |
    C_ii'45'case_390 T_Rii_70 T_Rii_70 T_Rii_70 |
    C_ii'45'arith_414 T_Rii_70 T_Rii_70 |
    C_ii'45'farith_438 T_Rii_70 T_Rii_70 |
    C_ii'45'il_462 T_Rii_70 T_Rii_70 |
    C_ii'45'ir_486 T_Rii_70 T_Rii_70 |
    C_ii'45'cmp_510 T_Rii_70 T_Rii_70 |
    C_ii'45'id'45'app_520 T_Rii_70 | C_ii'45'fst'45'app_530 T_Rii_70 |
    C_ii'45'snd'45'app_540 T_Rii_70 |
    C_ii'45'terminal'45'app_550 T_Rii_70 | C_ii'45'apply_560 T_Rii_70 |
    C_ii'45'apply'45'eff_570 T_Rii_70 | C_ii'45'Out_588 T_Rii_70 |
    C_ii'45'Out'45'eff_606 T_Rii_70 |
    C_ii'45'app_628 T_Rii_70 T_Rcc_82 |
    C_ii'45'effApp_650 T_Rii_70 T_Rcc_82 |
    C_ii'45'app'45'spine_672 T_Ric_96 T_Rdi_138 |
    C_ii'45'spine'45'app_694 T_Ric_96 T_Rdi_138 |
    C_ii'45'spine_716 T_Rii_70 T_Rdd_156
-- Once.TypeCheck.Route.Rcc
d_Rcc_82 a0 a1 a2 a3 a4 a5 a6 = ()
data T_Rcc_82
  = C_cc'45'sub'45'l_728 T_Ric_96 | C_cc'45'sub'45'r_740 T_Ric_96 |
    C_cc'45'id_742 | C_cc'45'fst_744 | C_cc'45'snd_746 |
    C_cc'45'terminal_748 | C_cc'45'initial_750 | C_cc'45'inl_752 |
    C_cc'45'inr_754 | C_cc'45'gg_772 T_Rdd_156 T_Rcc_82 |
    C_cc'45'gf_792 T_Rdc_114 T_Ric_96 |
    C_cc'45'fg_812 T_Rdc_114 T_Ric_96 |
    C_cc'45'ff_834 T_Rii_70 T_Rcc_82 |
    C_cc'45'copair_852 T_Rcc_82 T_Rcc_82 |
    C_cc'45'fork_870 T_Rcc_82 T_Rcc_82 | C_cc'45'curry_880 T_Rcc_82 |
    C_cc'45'cata_896 T_Rcc_82 | C_cc'45'ana_908 T_Rcc_82 |
    C_cc'45'lam_928 T_Rcc_82 |
    C_cc'45'pair'45'lit_946 T_Rcc_82 T_Rcc_82 |
    C_cc'45'In_962 T_Rcc_82 | C_cc'45'apply_972 T_Rii_70 |
    C_cc'45'inl'45'app_982 T_Rcc_82 | C_cc'45'inr'45'app_992 T_Rcc_82 |
    C_cc'45'initial'45'app_1002 T_Rcc_82 | C_cc'45'poly_1038
-- Once.TypeCheck.Route.Ric
d_Ric_96 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_Ric_96
  = C_ic'45'sub_1050 T_Rii_70 | C_ic'45'pair_1068 T_Ric_96 T_Ric_96 |
    C_ic'45'apply_1078 T_Rii_70
-- Once.TypeCheck.Route.Rdc
d_Rdc_114 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_Rdc_114
  = C_dc'45'infer_1092 T_Ric_96 | C_dc'45'sub_1104 T_Rdi_138 |
    C_dc'45'lam_1124 T_Ric_96 | C_dc'45'cg_1142 T_Rdd_156 T_Rdc_114 |
    C_dc'45'cf_1162 T_Rdi_138 T_Rdc_114 | C_dc'45'id_1164 |
    C_dc'45'fst_1166 | C_dc'45'snd_1168 | C_dc'45'terminal_1170 |
    C_dc'45'initial_1172 | C_dc'45'case_1190 T_Rdc_114 T_Rdc_114 |
    C_dc'45'pair_1208 T_Rdc_114 T_Rdc_114 |
    C_dc'45'cata_1224 T_Ric_96 | C_dc'45'poly_1270
-- Once.TypeCheck.Route.Rdi
d_Rdi_138 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = ()
newtype T_Rdi_138 = C_di'45'infer_1284 T_Rii_70
-- Once.TypeCheck.Route.Rdd
d_Rdd_156 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_Rdd_156
  = C_dd'45'infer'45'l_1298 T_Rdi_138 |
    C_dd'45'infer'45'r_1312 T_Rdi_138 | C_dd'45'lam_1332 T_Rii_70 |
    C_dd'45'compose_1350 T_Rdd_156 T_Rdd_156 | C_dd'45'id_1352 |
    C_dd'45'fst_1354 | C_dd'45'snd_1356 | C_dd'45'terminal_1358 |
    C_dd'45'initial_1360 | C_dd'45'case_1378 T_Rdd_156 T_Rdd_156 |
    C_dd'45'pair_1396 T_Rdd_156 T_Rdd_156 |
    C_dd'45'cata_1412 T_Rii_70 | C_dd'45'poly_1468
