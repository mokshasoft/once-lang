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

module MAlonzo.Code.Once.Spec.Surface.Generators where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Once.Spec.Core.Syntax
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.Spec.Surface.Generators.Gen
d_Gen_8 = ()
data T_Gen_8
  = C_id_10 | C_compose_12 | C_fst_14 | C_snd_16 | C_terminal_18 |
    C_pair_20 | C_inl_22 | C_inr_24 | C_initial_26 | C_case_28 |
    C_apply_30 | C_curry_32 | C_In_34 | C_cata_36 | C_Out_38 |
    C_ana_40 | C_unit_42 | C_toFloat_44
-- Once.Spec.Surface.Generators.word
d_word_46 :: T_Gen_8 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_word_46 v0
  = case coe v0 of
      C_id_10 -> coe ("id" :: Data.Text.Text)
      C_compose_12 -> coe ("compose" :: Data.Text.Text)
      C_fst_14 -> coe ("fst" :: Data.Text.Text)
      C_snd_16 -> coe ("snd" :: Data.Text.Text)
      C_terminal_18 -> coe ("terminal" :: Data.Text.Text)
      C_pair_20 -> coe ("pair" :: Data.Text.Text)
      C_inl_22 -> coe ("inl" :: Data.Text.Text)
      C_inr_24 -> coe ("inr" :: Data.Text.Text)
      C_initial_26 -> coe ("initial" :: Data.Text.Text)
      C_case_28 -> coe ("case" :: Data.Text.Text)
      C_apply_30 -> coe ("apply" :: Data.Text.Text)
      C_curry_32 -> coe ("curry" :: Data.Text.Text)
      C_In_34 -> coe ("In" :: Data.Text.Text)
      C_cata_36 -> coe ("cata" :: Data.Text.Text)
      C_Out_38 -> coe ("Out" :: Data.Text.Text)
      C_ana_40 -> coe ("ana" :: Data.Text.Text)
      C_unit_42 -> coe ("unit" :: Data.Text.Text)
      C_toFloat_44 -> coe ("toFloat" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Generators.GenWord
d_GenWord_48 :: MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d_GenWord_48 = erased
-- Once.Spec.Surface.Generators.Fixes
d_Fixes_54 = ()
data T_Fixes_54 = C_domain_56 | C_codomain_58 | C_both_60
-- Once.Spec.Surface.Generators.GenKind
d_GenKind_62 = ()
data T_GenKind_62
  = C_constant_64 | C_map_66 T_Fixes_54 | C_combinator_68 Integer
-- Once.Spec.Surface.Generators.kind
d_kind_70 :: T_Gen_8 -> T_GenKind_62
d_kind_70 v0
  = case coe v0 of
      C_id_10 -> coe C_map_66 (coe C_both_60)
      C_compose_12 -> coe C_combinator_68 (coe (2 :: Integer))
      C_fst_14 -> coe C_map_66 (coe C_domain_56)
      C_snd_16 -> coe C_map_66 (coe C_domain_56)
      C_terminal_18 -> coe C_map_66 (coe C_domain_56)
      C_pair_20 -> coe C_combinator_68 (coe (2 :: Integer))
      C_inl_22 -> coe C_map_66 (coe C_codomain_58)
      C_inr_24 -> coe C_map_66 (coe C_codomain_58)
      C_initial_26 -> coe C_map_66 (coe C_both_60)
      C_case_28 -> coe C_combinator_68 (coe (2 :: Integer))
      C_apply_30 -> coe C_map_66 (coe C_domain_56)
      C_curry_32 -> coe C_combinator_68 (coe (1 :: Integer))
      C_In_34 -> coe C_map_66 (coe C_codomain_58)
      C_cata_36 -> coe C_combinator_68 (coe (1 :: Integer))
      C_Out_38 -> coe C_map_66 (coe C_domain_56)
      C_ana_40 -> coe C_combinator_68 (coe (1 :: Integer))
      C_unit_42 -> coe C_constant_64
      C_toFloat_44 -> coe C_constant_64
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Spec.Surface.Generators.IsConstant
d_IsConstant_72 a0 = ()
data T_IsConstant_72 = C_is'45'constant_74
-- Once.Spec.Surface.Generators.IsMap
d_IsMap_76 a0 = ()
data T_IsMap_76 = C_is'45'map_80
-- Once.Spec.Surface.Generators.FromDomain
d_FromDomain_82 a0 = ()
data T_FromDomain_82 = C_fd'45'domain_84 | C_fd'45'both_86
-- Once.Spec.Surface.Generators.FromCodomain
d_FromCodomain_88 a0 = ()
data T_FromCodomain_88 = C_fc'45'codomain_90 | C_fc'45'both_92
-- Once.Spec.Surface.Generators.IsCombinator
d_IsCombinator_96 a0 a1 = ()
data T_IsCombinator_96 = C_is'45'combinator_100
-- Once.Spec.Surface.Generators._._⇒⟨_⟩_
d__'8658''10216'_'10217'__114 ::
  MAlonzo.Code.Once.Spec.Core.Syntax.T_Defs_24 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d__'8658''10216'_'10217'__114 ~v0 ~v1 ~v2 v3 v4 v5
  = du__'8658''10216'_'10217'__114 v3 v4 v5
du__'8658''10216'_'10217'__114 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
du__'8658''10216'_'10217'__114 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v0)
      (coe
         MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
         (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v1))
      (coe v2)
-- Once.Spec.Surface.Generators._.Constant
d_Constant_126 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_Constant_126 = C_k'45'unit_130 | C_k'45'toFloat_132
-- Once.Spec.Surface.Generators._.Morphism
d_Morphism_138 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
data T_Morphism_138
  = C_m'45'id_146 | C_m'45'fst_154 | C_m'45'snd_162 |
    C_m'45'terminal_168 | C_m'45'inl_176 | C_m'45'inr_184 |
    C_m'45'initial_190 | C_m'45'apply_200 |
    C_m'45'In_206 MAlonzo.Code.Once.Spec.Type.T_WFFun_118 |
    C_m'45'Out_214 MAlonzo.Code.Once.Spec.Type.T_WFFun_118
-- Once.Spec.Surface.Generators._.Final
d_Final_220 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
data T_Final_220
  = C_final'45'ν_234 MAlonzo.Code.Once.Spec.Grade.T__'8849'π__50
                     MAlonzo.Code.Once.Spec.Type.T_WFFun_118 |
    C_final'45'T'8734'_240
