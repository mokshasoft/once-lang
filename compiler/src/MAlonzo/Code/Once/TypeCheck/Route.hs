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
    C_ii'45'unit'45'var_174 | C_ii'45'resolved_190 | C_ii'45'own_202 |
    C_ii'45'local_218 | C_ii'45'import_238 |
    C_ii'45'poly'45'infer_278 | C_ii'45'annot_292 T_Rcc_82 |
    C_ii'45'pair_310 T_Rii_70 T_Rii_70 | C_ii'45'neg_320 T_Rii_70 |
    C_ii'45'neg'45'float_330 | C_ii'45'let_350 T_Rii_70 T_Rii_70 |
    C_ii'45'case_400 T_Rii_70 T_Rii_70 T_Rii_70 |
    C_ii'45'arith_424 T_Rii_70 T_Rii_70 |
    C_ii'45'farith_448 T_Rii_70 T_Rii_70 |
    C_ii'45'il_472 T_Rii_70 T_Rii_70 |
    C_ii'45'ir_496 T_Rii_70 T_Rii_70 |
    C_ii'45'cmp_520 T_Rii_70 T_Rii_70 |
    C_ii'45'id'45'app_530 T_Rii_70 | C_ii'45'fst'45'app_540 T_Rii_70 |
    C_ii'45'snd'45'app_550 T_Rii_70 |
    C_ii'45'terminal'45'app_560 T_Rii_70 | C_ii'45'apply_570 T_Rii_70 |
    C_ii'45'apply'45'eff_588 T_Rii_70 | C_ii'45'Out_606 T_Rii_70 |
    C_ii'45'Out'45'eff_624 T_Rii_70 |
    C_ii'45'app_646 T_Rii_70 T_Rcc_82 |
    C_ii'45'effApp_672 T_Rii_70 T_Rcc_82 |
    C_ii'45'app'45'spine_694 T_Ric_96 T_Rdi_138 |
    C_ii'45'spine'45'app_716 T_Ric_96 T_Rdi_138 |
    C_ii'45'spine_738 T_Rii_70 T_Rdd_156
-- Once.TypeCheck.Route.Rcc
d_Rcc_82 a0 a1 a2 a3 a4 a5 a6 = ()
data T_Rcc_82
  = C_cc'45'sub'45'l_750 T_Ric_96 | C_cc'45'sub'45'r_762 T_Ric_96 |
    C_cc'45'id_768 | C_cc'45'fst_774 | C_cc'45'snd_780 |
    C_cc'45'terminal_786 | C_cc'45'initial_792 | C_cc'45'inl_798 |
    C_cc'45'inr_804 | C_cc'45'gg_822 T_Rdd_156 T_Rcc_82 |
    C_cc'45'gf_842 T_Rdc_114 T_Ric_96 |
    C_cc'45'fg_862 T_Rdc_114 T_Ric_96 |
    C_cc'45'ff_884 T_Rii_70 T_Rcc_82 |
    C_cc'45'copair_902 T_Rcc_82 T_Rcc_82 |
    C_cc'45'fork_920 T_Rcc_82 T_Rcc_82 | C_cc'45'curry_934 T_Rcc_82 |
    C_cc'45'cata_954 T_Rcc_82 | C_cc'45'ana_980 T_Rcc_82 |
    C_cc'45'loop_990 T_Rcc_82 | C_cc'45'lam_1014 T_Rcc_82 |
    C_cc'45'pair'45'lit_1032 T_Rcc_82 T_Rcc_82 |
    C_cc'45'In_1048 T_Rcc_82 | C_cc'45'apply_1058 T_Rii_70 |
    C_cc'45'inl'45'app_1068 T_Rcc_82 |
    C_cc'45'inr'45'app_1078 T_Rcc_82 |
    C_cc'45'initial'45'app_1088 T_Rcc_82 | C_cc'45'poly_1124
-- Once.TypeCheck.Route.Ric
d_Ric_96 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_Ric_96
  = C_ic'45'sub_1136 T_Rii_70 | C_ic'45'pair_1154 T_Ric_96 T_Ric_96 |
    C_ic'45'apply_1164 T_Rii_70
-- Once.TypeCheck.Route.Rdc
d_Rdc_114 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_Rdc_114
  = C_dc'45'infer_1178 T_Ric_96 | C_dc'45'sub_1190 T_Rdi_138 |
    C_dc'45'lam_1212 T_Ric_96 | C_dc'45'cg_1230 T_Rdd_156 T_Rdc_114 |
    C_dc'45'cf_1250 T_Rdi_138 T_Rdc_114 | C_dc'45'id_1256 |
    C_dc'45'fst_1262 | C_dc'45'snd_1268 | C_dc'45'terminal_1274 |
    C_dc'45'initial_1280 | C_dc'45'case_1304 T_Rdc_114 T_Rdc_114 |
    C_dc'45'pair_1322 T_Rdc_114 T_Rdc_114 |
    C_dc'45'cata_1342 T_Ric_96 | C_dc'45'poly_1388
-- Once.TypeCheck.Route.Rdi
d_Rdi_138 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = ()
newtype T_Rdi_138 = C_di'45'infer_1402 T_Rii_70
-- Once.TypeCheck.Route.Rdd
d_Rdd_156 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_Rdd_156
  = C_dd'45'infer'45'l_1416 T_Rdi_138 |
    C_dd'45'infer'45'r_1430 T_Rdi_138 | C_dd'45'lam_1450 T_Rii_70 |
    C_dd'45'compose_1468 T_Rdd_156 T_Rdd_156 | C_dd'45'id_1474 |
    C_dd'45'fst_1480 | C_dd'45'snd_1486 | C_dd'45'terminal_1492 |
    C_dd'45'initial_1498 | C_dd'45'case_1528 T_Rdd_156 T_Rdd_156 |
    C_dd'45'pair_1546 T_Rdd_156 T_Rdd_156 |
    C_dd'45'cata_1566 T_Rii_70 | C_dd'45'poly_1622
