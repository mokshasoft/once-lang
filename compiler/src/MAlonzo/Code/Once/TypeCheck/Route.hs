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
    C_ii'45'local_222 | C_ii'45'import_242 |
    C_ii'45'poly'45'infer_282 | C_ii'45'annot_296 T_Rcc_82 |
    C_ii'45'pair_314 T_Rii_70 T_Rii_70 | C_ii'45'neg_324 T_Rii_70 |
    C_ii'45'neg'45'float_334 | C_ii'45'let_354 T_Rii_70 T_Rii_70 |
    C_ii'45'case_392 T_Rii_70 T_Rii_70 T_Rii_70 |
    C_ii'45'arith_416 T_Rii_70 T_Rii_70 |
    C_ii'45'farith_440 T_Rii_70 T_Rii_70 |
    C_ii'45'il_464 T_Rii_70 T_Rii_70 |
    C_ii'45'ir_488 T_Rii_70 T_Rii_70 |
    C_ii'45'cmp_512 T_Rii_70 T_Rii_70 |
    C_ii'45'id'45'app_522 T_Rii_70 | C_ii'45'fst'45'app_532 T_Rii_70 |
    C_ii'45'snd'45'app_542 T_Rii_70 |
    C_ii'45'terminal'45'app_552 T_Rii_70 | C_ii'45'apply_562 T_Rii_70 |
    C_ii'45'apply'45'eff_580 T_Rii_70 | C_ii'45'Out_598 T_Rii_70 |
    C_ii'45'Out'45'eff_616 T_Rii_70 |
    C_ii'45'app_638 T_Rii_70 T_Rcc_82 |
    C_ii'45'effApp_664 T_Rii_70 T_Rcc_82 |
    C_ii'45'app'45'spine_686 T_Ric_96 T_Rdi_138 |
    C_ii'45'spine'45'app_708 T_Ric_96 T_Rdi_138 |
    C_ii'45'spine_730 T_Rii_70 T_Rdd_156
-- Once.TypeCheck.Route.Rcc
d_Rcc_82 a0 a1 a2 a3 a4 a5 a6 = ()
data T_Rcc_82
  = C_cc'45'sub'45'l_742 T_Ric_96 | C_cc'45'sub'45'r_754 T_Ric_96 |
    C_cc'45'id_760 | C_cc'45'fst_766 | C_cc'45'snd_772 |
    C_cc'45'terminal_778 | C_cc'45'initial_784 | C_cc'45'inl_790 |
    C_cc'45'inr_796 | C_cc'45'gg_814 T_Rdd_156 T_Rcc_82 |
    C_cc'45'gf_834 T_Rdc_114 T_Ric_96 |
    C_cc'45'fg_854 T_Rdc_114 T_Ric_96 |
    C_cc'45'ff_876 T_Rii_70 T_Rcc_82 |
    C_cc'45'copair_894 T_Rcc_82 T_Rcc_82 |
    C_cc'45'fork_912 T_Rcc_82 T_Rcc_82 | C_cc'45'curry_926 T_Rcc_82 |
    C_cc'45'cata_946 T_Rcc_82 | C_cc'45'ana_972 T_Rcc_82 |
    C_cc'45'loop_982 T_Rcc_82 | C_cc'45'lam_1006 T_Rcc_82 |
    C_cc'45'pair'45'lit_1024 T_Rcc_82 T_Rcc_82 |
    C_cc'45'In_1040 T_Rcc_82 | C_cc'45'apply_1050 T_Rii_70 |
    C_cc'45'inl'45'app_1060 T_Rcc_82 |
    C_cc'45'inr'45'app_1070 T_Rcc_82 |
    C_cc'45'initial'45'app_1080 T_Rcc_82 | C_cc'45'poly_1116
-- Once.TypeCheck.Route.Ric
d_Ric_96 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_Ric_96
  = C_ic'45'sub_1128 T_Rii_70 | C_ic'45'pair_1146 T_Ric_96 T_Ric_96 |
    C_ic'45'apply_1156 T_Rii_70
-- Once.TypeCheck.Route.Rdc
d_Rdc_114 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_Rdc_114
  = C_dc'45'infer_1170 T_Ric_96 | C_dc'45'sub_1182 T_Rdi_138 |
    C_dc'45'lam_1204 T_Ric_96 | C_dc'45'cg_1222 T_Rdd_156 T_Rdc_114 |
    C_dc'45'cf_1242 T_Rdi_138 T_Rdc_114 | C_dc'45'id_1248 |
    C_dc'45'fst_1254 | C_dc'45'snd_1260 | C_dc'45'terminal_1266 |
    C_dc'45'initial_1272 | C_dc'45'case_1290 T_Rdc_114 T_Rdc_114 |
    C_dc'45'pair_1308 T_Rdc_114 T_Rdc_114 |
    C_dc'45'cata_1328 T_Ric_96 | C_dc'45'poly_1374
-- Once.TypeCheck.Route.Rdi
d_Rdi_138 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = ()
newtype T_Rdi_138 = C_di'45'infer_1388 T_Rii_70
-- Once.TypeCheck.Route.Rdd
d_Rdd_156 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_Rdd_156
  = C_dd'45'infer'45'l_1402 T_Rdi_138 |
    C_dd'45'infer'45'r_1416 T_Rdi_138 | C_dd'45'lam_1436 T_Rii_70 |
    C_dd'45'compose_1454 T_Rdd_156 T_Rdd_156 | C_dd'45'id_1460 |
    C_dd'45'fst_1466 | C_dd'45'snd_1472 | C_dd'45'terminal_1478 |
    C_dd'45'initial_1484 | C_dd'45'case_1502 T_Rdd_156 T_Rdd_156 |
    C_dd'45'pair_1520 T_Rdd_156 T_Rdd_156 |
    C_dd'45'cata_1540 T_Rii_70 | C_dd'45'poly_1596
