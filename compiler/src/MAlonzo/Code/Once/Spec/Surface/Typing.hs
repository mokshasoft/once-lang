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

module MAlonzo.Code.Once.Spec.Surface.Typing where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.Spec.Core.Syntax
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Signature
import qualified MAlonzo.Code.Once.Spec.Sub
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Spec.Surface.Typing.Locals
d_Locals_18 a0 a1 a2 a3 a4 a5 = ()
data T_Locals_18
  = C_'8709'_22 |
    C__'9657'_'8758'__26 T_Locals_18
                         MAlonzo.Code.Agda.Builtin.String.T_String_6
                         MAlonzo.Code.Once.Spec.Type.T_Ty_8
-- Once.Spec.Surface.Typing._∋_⦂_at_
d__'8715'_'10626'_at__32 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T__'8715'_'10626'_at__32
  = C_here_44 | C_there_60 T__'8715'_'10626'_at__32
-- Once.Spec.Surface.Typing.↑
d_'8593'_64 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6) ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_'8593'_64 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_'8593'_64 v4 v5
du_'8593'_64 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
du_'8593'_64 v0 v1
  = coe
      MAlonzo.Code.Once.Spec.Type.d__'10216'_'10217'_154
      (coe (0 :: Integer)) (coe v0) (coe v1) erased
-- Once.Spec.Surface.Typing._⇒⟨_⟩_
d__'8658''10216'_'10217'__70 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6) ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d__'8658''10216'_'10217'__70 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du__'8658''10216'_'10217'__70 v5 v6 v7
du__'8658''10216'_'10217'__70 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
du__'8658''10216'_'10217'__70 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v1))
      (coe v2)
-- Once.Spec.Surface.Typing.IntArith
d_IntArith_78 a0 a1 a2 a3 a4 a5 = ()
data T_IntArith_78
  = C_ia'45'add_80 | C_ia'45'sub_82 | C_ia'45'mul_84 |
    C_ia'45'div_86 | C_ia'45'mod_88
-- Once.Spec.Surface.Typing.FloatArith
d_FloatArith_90 a0 a1 a2 a3 a4 a5 = ()
data T_FloatArith_90
  = C_fa'45'add_92 | C_fa'45'sub_94 | C_fa'45'mul_96 | C_fa'45'div_98
-- Once.Spec.Surface.Typing.Compare
d_Compare_100 a0 a1 a2 a3 a4 a5 = ()
data T_Compare_100
  = C_cmp'45'lt_102 | C_cmp'45'le_104 | C_cmp'45'gt_106 |
    C_cmp'45'ge_108 | C_cmp'45'eq_110 | C_cmp'45'ne_112
-- Once.Spec.Surface.Typing.specialGenerators
d_specialGenerators_114 ::
  [MAlonzo.Code.Once.Spec.Signature.T_Decl_114] ->
  Integer ->
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_specialGenerators_114 ~v0 ~v1 ~v2 ~v3 = du_specialGenerators_114
du_specialGenerators_114 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
du_specialGenerators_114
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe ("id" :: Data.Text.Text))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe ("fst" :: Data.Text.Text))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe ("snd" :: Data.Text.Text))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe ("terminal" :: Data.Text.Text))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                  (coe ("inl" :: Data.Text.Text))
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe ("inr" :: Data.Text.Text))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                        (coe ("initial" :: Data.Text.Text))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe ("curry" :: Data.Text.Text))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe ("apply" :: Data.Text.Text))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe ("In" :: Data.Text.Text))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe ("cata" :: Data.Text.Text))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe ("ana" :: Data.Text.Text))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe ("Out" :: Data.Text.Text))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))))))
-- Once.Spec.Surface.Typing.SpecialHead
d_SpecialHead_116 a0 a1 a2 a3 a4 = ()
data T_SpecialHead_116
  = C_sh'45'gen_120 MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 |
    C_sh'45'pair_124 | C_sh'45'compose_128 | C_sh'45'case_132
-- Once.Spec.Surface.Typing._._⊢_⇒_↝_
d__'8866'_'8658'_'8605'__146 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
data T__'8866'_'8658'_'8605'__146
  = C_s'45'int_166 | C_s'45'float_174 | C_s'45'unit_176 |
    C_s'45'unit'45'g_178 | C_s'45'var_186 T__'8715'_'10626'_at__32 |
    C_s'45'sigop_192 MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
                     MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 |
    C_s'45'def_200 | C_s'45'annot_208 T__'8866'_'8656'_'8605'__152 |
    C_s'45'pair_222 T__'8866'_'8658'_'8605'__146
                    T__'8866'_'8658'_'8605'__146 |
    C_s'45'neg_228 T__'8866'_'8658'_'8605'__146 |
    C_s'45'neg'45'float_236 |
    C_s'45'let_254 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                   T__'8866'_'8658'_'8605'__146 T__'8866'_'8658'_'8605'__146 |
    C_s'45'case_286 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                    MAlonzo.Code.Once.Spec.Type.T_Ty_8 T__'8866'_'8658'_'8605'__146
                    T__'8866'_'8658'_'8605'__146 T__'8866'_'8658'_'8605'__146
                    MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 |
    C_s'45'arith_300 T_IntArith_78 T__'8866'_'8658'_'8605'__146
                     T__'8866'_'8658'_'8605'__146 |
    C_s'45'arith'45'float_314 T_FloatArith_90
                              T__'8866'_'8658'_'8605'__146 T__'8866'_'8658'_'8605'__146 |
    C_s'45'arith'45'float'45'il_328 T_FloatArith_90
                                    T__'8866'_'8658'_'8605'__146 T__'8866'_'8658'_'8605'__146 |
    C_s'45'arith'45'float'45'ir_342 T_FloatArith_90
                                    T__'8866'_'8658'_'8605'__146 T__'8866'_'8658'_'8605'__146 |
    C_s'45'compare_356 T_Compare_100 T__'8866'_'8658'_'8605'__146
                       T__'8866'_'8658'_'8605'__146 |
    C_s'45'id'45'app_364 T__'8866'_'8658'_'8605'__146 |
    C_s'45'fst'45'app_374 T__'8866'_'8658'_'8605'__146 |
    C_s'45'snd'45'app_384 T__'8866'_'8658'_'8605'__146 |
    C_s'45'terminal'45'app_392 T__'8866'_'8658'_'8605'__146 |
    C_s'45'apply'45'app_402 T__'8866'_'8658'_'8605'__146 |
    C_s'45'apply'45'eff'45'app_414 MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68
                                   T__'8866'_'8658'_'8605'__146 |
    C_s'45'Out'45'app_422 MAlonzo.Code.Once.Spec.Type.T_WFFun_118
                          T__'8866'_'8658'_'8605'__146 |
    C_s'45'Out'45'act'45'app_430 MAlonzo.Code.Once.Spec.Type.T_WFFun_118
                                 T__'8866'_'8658'_'8605'__146 |
    C_s'45'app_446 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                   MAlonzo.Code.Once.Spec.Grade.T_Quantity_6
                   T__'8866'_'8658'_'8605'__146 T__'8866'_'8656'_'8605'__152 |
    C_s'45'effApp_462 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                      MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
                      MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
                      MAlonzo.Code.Once.Spec.Grade.T_EffGrade_68
                      T__'8866'_'8658'_'8605'__146 T__'8866'_'8656'_'8605'__152 |
    C_s'45'app'45'spine_476 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                            T__'8866'_'8658'_'8605'__146
                            T__'8866'_'8656'_'8658''91'_'93''8614'_'8605'__158
-- Once.Spec.Surface.Typing._._⊢_⇐_↝_
d__'8866'_'8656'_'8605'__152 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
data T__'8866'_'8656'_'8605'__152
  = C_c'45'id_486 | C_c'45'fst_494 | C_c'45'snd_502 |
    C_c'45'terminal_508 | C_c'45'initial_514 | C_c'45'inl_522 |
    C_c'45'inr_530 |
    C_c'45'compose'45'g_548 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                            MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
                            T__'8866'_'8656'_'8658''91'_'93''8614'_'8605'__158
                            T__'8866'_'8656'_'8605'__152 |
    C_c'45'compose'45'f_570 MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
                            T__'8866'_'8658'_'8605'__146
                            MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8
                            T__'8866'_'8656'_'8605'__152 |
    C_c'45'case_588 MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
                    T__'8866'_'8656'_'8605'__152 T__'8866'_'8656'_'8605'__152 |
    C_c'45'pair_606 MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
                    T__'8866'_'8656'_'8605'__152 T__'8866'_'8656'_'8605'__152 |
    C_c'45'curry_622 T__'8866'_'8656'_'8605'__152 |
    C_c'45'cata_634 MAlonzo.Code.Once.Spec.Type.T_WFFun_118
                    T__'8866'_'8656'_'8605'__152 |
    C_c'45'ana_648 MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
                   MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
                   MAlonzo.Code.Once.Spec.Type.T_WFFun_118
                   T__'8866'_'8656'_'8605'__152 |
    C_c'45'loop_658 T__'8866'_'8656'_'8605'__152 |
    C_c'45'sub_668 T__'8866'_'8658'_'8605'__146
                   MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 |
    C_c'45'lam_684 T__'8866'_'8656'_'8605'__152 |
    C_c'45'pair'45'lit_698 T__'8866'_'8656'_'8605'__152
                           T__'8866'_'8656'_'8605'__152 |
    C_c'45'In'45'app_706 MAlonzo.Code.Once.Spec.Type.T_WFFun_118
                         T__'8866'_'8656'_'8605'__152 |
    C_c'45'apply'45'app_716 T__'8866'_'8658'_'8605'__146 |
    C_c'45'inl'45'app_726 T__'8866'_'8656'_'8605'__152 |
    C_c'45'inr'45'app_736 T__'8866'_'8656'_'8605'__152 |
    C_c'45'initial'45'app_744 T__'8866'_'8656'_'8605'__152 |
    C_c'45'poly_752 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                    (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
                     MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                     MAlonzo.Code.Once.Spec.Type.T_Base_84)
-- Once.Spec.Surface.Typing._._⊢_⇐_⇒[_]↦_↝_
d__'8866'_'8656'_'8658''91'_'93''8614'_'8605'__158 a0 a1 a2 a3 a4
                                                   a5 a6 a7 a8 a9 a10 a11 a12
  = ()
data T__'8866'_'8656'_'8658''91'_'93''8614'_'8605'__158
  = C_d'45'infer_772 T__'8866'_'8658'_'8605'__146
                     MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8
                     MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_d'45'poly_794 MAlonzo.Code.Data.Nat.Base.T__'8804'__22
                    MAlonzo.Code.Once.Spec.Type.T_Ty_8
                    MAlonzo.Code.Once.Spec.Type.T_Ty_8
                    (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
                     MAlonzo.Code.Once.Spec.Type.T_Occurs_240 ->
                     MAlonzo.Code.Once.Spec.Type.T_Occurs_240)
                    (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
                     MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
                     MAlonzo.Code.Once.Spec.Type.T_Base_84)
                    MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50 |
    C_d'45'lam_808 T__'8866'_'8658'_'8605'__146 |
    C_d'45'compose_826 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                       MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
                       T__'8866'_'8656'_'8658''91'_'93''8614'_'8605'__158
                       T__'8866'_'8656'_'8658''91'_'93''8614'_'8605'__158 |
    C_d'45'id_832 | C_d'45'fst_840 | C_d'45'snd_848 |
    C_d'45'terminal_854 | C_d'45'initial_858 |
    C_d'45'case_880 MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
                    T__'8866'_'8656'_'8658''91'_'93''8614'_'8605'__158
                    T__'8866'_'8656'_'8658''91'_'93''8614'_'8605'__158
                    MAlonzo.Code.Once.Spec.Sub.T__'8852'_'8788'__148 |
    C_d'45'pair_898 MAlonzo.Code.Once.Spec.Core.Syntax.T_Tm_102
                    T__'8866'_'8656'_'8658''91'_'93''8614'_'8605'__158
                    T__'8866'_'8656'_'8658''91'_'93''8614'_'8605'__158 |
    C_d'45'cata_910 MAlonzo.Code.Once.Spec.Type.T_WFFun_118
                    T__'8866'_'8658'_'8605'__146
