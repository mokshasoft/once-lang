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
    C_ii'45'apply'45'eff_586 T_Rii_70 | C_ii'45'Out_604 T_Rii_70 |
    C_ii'45'Out'45'eff_622 T_Rii_70 |
    C_ii'45'app_644 T_Rii_70 T_Rcc_82 |
    C_ii'45'effApp_666 T_Rii_70 T_Rcc_82 |
    C_ii'45'app'45'spine_688 T_Ric_96 T_Rdi_138 |
    C_ii'45'spine'45'app_710 T_Ric_96 T_Rdi_138 |
    C_ii'45'spine_732 T_Rii_70 T_Rdd_156
-- Once.TypeCheck.Route.Rcc
d_Rcc_82 a0 a1 a2 a3 a4 a5 a6 = ()
data T_Rcc_82
  = C_cc'45'sub'45'l_744 T_Ric_96 | C_cc'45'sub'45'r_756 T_Ric_96 |
    C_cc'45'id_758 | C_cc'45'fst_760 | C_cc'45'snd_762 |
    C_cc'45'terminal_764 | C_cc'45'initial_766 | C_cc'45'inl_768 |
    C_cc'45'inr_770 | C_cc'45'gg_788 T_Rdd_156 T_Rcc_82 |
    C_cc'45'gf_808 T_Rdc_114 T_Ric_96 |
    C_cc'45'fg_828 T_Rdc_114 T_Ric_96 |
    C_cc'45'ff_850 T_Rii_70 T_Rcc_82 |
    C_cc'45'copair_868 T_Rcc_82 T_Rcc_82 |
    C_cc'45'fork_886 T_Rcc_82 T_Rcc_82 | C_cc'45'curry_896 T_Rcc_82 |
    C_cc'45'cata_912 T_Rcc_82 | C_cc'45'ana_928 T_Rcc_82 |
    C_cc'45'lam_948 T_Rcc_82 |
    C_cc'45'pair'45'lit_966 T_Rcc_82 T_Rcc_82 |
    C_cc'45'In_982 T_Rcc_82 | C_cc'45'apply_992 T_Rii_70 |
    C_cc'45'inl'45'app_1002 T_Rcc_82 |
    C_cc'45'inr'45'app_1012 T_Rcc_82 |
    C_cc'45'initial'45'app_1022 T_Rcc_82 | C_cc'45'poly_1058
-- Once.TypeCheck.Route.Ric
d_Ric_96 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_Ric_96
  = C_ic'45'sub_1070 T_Rii_70 | C_ic'45'pair_1088 T_Ric_96 T_Ric_96 |
    C_ic'45'apply_1098 T_Rii_70
-- Once.TypeCheck.Route.Rdc
d_Rdc_114 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_Rdc_114
  = C_dc'45'infer_1112 T_Ric_96 | C_dc'45'sub_1124 T_Rdi_138 |
    C_dc'45'lam_1144 T_Ric_96 | C_dc'45'cg_1162 T_Rdd_156 T_Rdc_114 |
    C_dc'45'cf_1182 T_Rdi_138 T_Rdc_114 | C_dc'45'id_1184 |
    C_dc'45'fst_1186 | C_dc'45'snd_1188 | C_dc'45'terminal_1190 |
    C_dc'45'initial_1192 | C_dc'45'case_1210 T_Rdc_114 T_Rdc_114 |
    C_dc'45'pair_1228 T_Rdc_114 T_Rdc_114 |
    C_dc'45'cata_1244 T_Ric_96 | C_dc'45'poly_1290
-- Once.TypeCheck.Route.Rdi
d_Rdi_138 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = ()
newtype T_Rdi_138 = C_di'45'infer_1304 T_Rii_70
-- Once.TypeCheck.Route.Rdd
d_Rdd_156 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_Rdd_156
  = C_dd'45'infer'45'l_1318 T_Rdi_138 |
    C_dd'45'infer'45'r_1332 T_Rdi_138 | C_dd'45'lam_1352 T_Rii_70 |
    C_dd'45'compose_1370 T_Rdd_156 T_Rdd_156 | C_dd'45'id_1372 |
    C_dd'45'fst_1374 | C_dd'45'snd_1376 | C_dd'45'terminal_1378 |
    C_dd'45'initial_1380 | C_dd'45'case_1398 T_Rdd_156 T_Rdd_156 |
    C_dd'45'pair_1416 T_Rdd_156 T_Rdd_156 |
    C_dd'45'cata_1432 T_Rii_70 | C_dd'45'poly_1488
