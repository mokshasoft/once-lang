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

module MAlonzo.Code.Once.LinCore.TyEq where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Once.LinCore.Core
import qualified MAlonzo.Code.Once.LinCore.Flat
import qualified MAlonzo.Code.Once.Spec.Numerics

-- Once.LinCore.TyEq._.Gr
d_Gr_52 a0 = ()
-- Once.LinCore.TyEq._.Kd
d_Kd_58 a0 = ()
-- Once.LinCore.TyEq._.LF
d_LF_66 a0 = ()
-- Once.LinCore.TyEq._.LTy
d_LTy_72 a0 = ()
-- Once.LinCore.TyEq.Tr
d_Tr_686 a0 = ()
data T_Tr_686
  = C_lf_688 | C_nd_690 Integer T_Tr_686 T_Tr_686 T_Tr_686 T_Tr_686
-- Once.LinCore.TyEq.eqTr
d_eqTr_692 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Tr_686 -> T_Tr_686 -> Bool
d_eqTr_692 ~v0 v1 v2 = du_eqTr_692 v1 v2
du_eqTr_692 :: T_Tr_686 -> T_Tr_686 -> Bool
du_eqTr_692 v0 v1
  = case coe v0 of
      C_lf_688
        -> case coe v1 of
             C_lf_688 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
             C_nd_690 v2 v3 v4 v5 v6
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nd_690 v2 v3 v4 v5 v6
        -> case coe v1 of
             C_lf_688 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_nd_690 v7 v8 v9 v10 v11
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                    (coe eqInt (coe v2) (coe v7))
                    (coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe du_eqTr_692 (coe v3) (coe v8))
                       (coe
                          MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                          (coe du_eqTr_692 (coe v4) (coe v9))
                          (coe
                             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                             (coe du_eqTr_692 (coe v5) (coe v10))
                             (coe du_eqTr_692 (coe v6) (coe v11)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.TyEq.∧-l
d_'8743''45'l_718 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'l_718 = erased
-- Once.LinCore.TyEq.∧-r
d_'8743''45'r_724 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'r_724 = erased
-- Once.LinCore.TyEq.∧-i
d_'8743''45'i_732 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Bool ->
  Bool ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'i_732 = erased
-- Once.LinCore.TyEq.toT
d_toT_736 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Bool -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_toT_736 ~v0 v1 ~v2 = du_toT_736 v1
du_toT_736 :: Bool -> AgdaAny
du_toT_736 v0
  = coe seq (coe v0) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Once.LinCore.TyEq.≡ᵇ-refl
d_'8801''7495''45'refl_740 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''45'refl_740 = erased
-- Once.LinCore.TyEq.eqTr-ok
d_eqTr'45'ok_748 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Tr_686 ->
  T_Tr_686 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eqTr'45'ok_748 = erased
-- Once.LinCore.TyEq.eqTr-refl
d_eqTr'45'refl_788 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Tr_686 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eqTr'45'refl_788 = erased
-- Once.LinCore.TyEq.tag
d_tag_800 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> T_Tr_686
d_tag_800 ~v0 v1 = du_tag_800 v1
du_tag_800 :: Integer -> T_Tr_686
du_tag_800 v0
  = coe
      C_nd_690 (coe v0) (coe C_lf_688) (coe C_lf_688) (coe C_lf_688)
      (coe C_lf_688)
-- Once.LinCore.TyEq.tagOf
d_tagOf_804 :: T_Tr_686 -> Integer
d_tagOf_804 v0
  = case coe v0 of
      C_lf_688 -> coe (0 :: Integer)
      C_nd_690 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.TyEq.encB
d_encB_808 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> T_Tr_686
d_encB_808 ~v0 v1 = du_encB_808 v1
du_encB_808 :: MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> T_Tr_686
du_encB_808 v0
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Flat.C_int_48
        -> coe du_tag_800 (coe (0 :: Integer))
      MAlonzo.Code.Once.LinCore.Flat.C_float_50
        -> coe du_tag_800 (coe (1 :: Integer))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.TyEq.pickB
d_pickB_810 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> MAlonzo.Code.Once.LinCore.Flat.T_Base_46
d_pickB_810 ~v0 v1 = du_pickB_810 v1
du_pickB_810 :: Integer -> MAlonzo.Code.Once.LinCore.Flat.T_Base_46
du_pickB_810 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Once.LinCore.Flat.C_int_48
      1 -> coe MAlonzo.Code.Once.LinCore.Flat.C_float_50
      _ -> coe MAlonzo.Code.Once.LinCore.Flat.C_int_48
-- Once.LinCore.TyEq.decB
d_decB_812 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Tr_686 -> MAlonzo.Code.Once.LinCore.Flat.T_Base_46
d_decB_812 ~v0 v1 = du_decB_812 v1
du_decB_812 :: T_Tr_686 -> MAlonzo.Code.Once.LinCore.Flat.T_Base_46
du_decB_812 v0 = coe du_pickB_810 (coe d_tagOf_804 (coe v0))
-- Once.LinCore.TyEq.encK
d_encK_816 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Kd_150 -> T_Tr_686
d_encK_816 ~v0 v1 = du_encK_816 v1
du_encK_816 :: MAlonzo.Code.Once.LinCore.Core.T_Kd_150 -> T_Tr_686
du_encK_816 v0
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_once_152
        -> coe du_tag_800 (coe (0 :: Integer))
      MAlonzo.Code.Once.LinCore.Core.C_many_154
        -> coe du_tag_800 (coe (1 :: Integer))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.TyEq.pickK
d_pickK_818 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> MAlonzo.Code.Once.LinCore.Core.T_Kd_150
d_pickK_818 ~v0 v1 = du_pickK_818 v1
du_pickK_818 :: Integer -> MAlonzo.Code.Once.LinCore.Core.T_Kd_150
du_pickK_818 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Once.LinCore.Core.C_once_152
      1 -> coe MAlonzo.Code.Once.LinCore.Core.C_many_154
      _ -> coe MAlonzo.Code.Once.LinCore.Core.C_once_152
-- Once.LinCore.TyEq.decK
d_decK_820 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Tr_686 -> MAlonzo.Code.Once.LinCore.Core.T_Kd_150
d_decK_820 ~v0 v1 = du_decK_820 v1
du_decK_820 :: T_Tr_686 -> MAlonzo.Code.Once.LinCore.Core.T_Kd_150
du_decK_820 v0 = coe du_pickK_818 (coe d_tagOf_804 (coe v0))
-- Once.LinCore.TyEq.encG
d_encG_824 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 -> T_Tr_686
d_encG_824 ~v0 v1 = du_encG_824 v1
du_encG_824 :: MAlonzo.Code.Once.LinCore.Core.T_Gr_156 -> T_Tr_686
du_encG_824 v0
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_act_158
        -> coe du_tag_800 (coe (0 :: Integer))
      MAlonzo.Code.Once.LinCore.Core.C_eff_160
        -> coe du_tag_800 (coe (1 :: Integer))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.TyEq.pickG
d_pickG_826 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> MAlonzo.Code.Once.LinCore.Core.T_Gr_156
d_pickG_826 ~v0 v1 = du_pickG_826 v1
du_pickG_826 :: Integer -> MAlonzo.Code.Once.LinCore.Core.T_Gr_156
du_pickG_826 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Once.LinCore.Core.C_act_158
      1 -> coe MAlonzo.Code.Once.LinCore.Core.C_eff_160
      _ -> coe MAlonzo.Code.Once.LinCore.Core.C_act_158
-- Once.LinCore.TyEq.decG
d_decG_828 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Tr_686 -> MAlonzo.Code.Once.LinCore.Core.T_Gr_156
d_decG_828 ~v0 v1 = du_decG_828 v1
du_decG_828 :: T_Tr_686 -> MAlonzo.Code.Once.LinCore.Core.T_Gr_156
du_decG_828 v0 = coe du_pickG_826 (coe d_tagOf_804 (coe v0))
-- Once.LinCore.TyEq.encF
d_encF_832 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 -> T_Tr_686
d_encF_832 ~v0 v1 = du_encF_832 v1
du_encF_832 :: MAlonzo.Code.Once.LinCore.Core.T_LF_134 -> T_Tr_686
du_encF_832 v0
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_Idf_136
        -> coe du_tag_800 (coe (0 :: Integer))
      MAlonzo.Code.Once.LinCore.Core.C_Kone_138
        -> coe du_tag_800 (coe (1 :: Integer))
      MAlonzo.Code.Once.LinCore.Core.C_Kzero_140
        -> coe du_tag_800 (coe (2 :: Integer))
      MAlonzo.Code.Once.LinCore.Core.C_Kb_142 v1
        -> coe
             C_nd_690 (coe (3 :: Integer)) (coe du_encB_808 (coe v1))
             (coe C_lf_688) (coe C_lf_688) (coe C_lf_688)
      MAlonzo.Code.Once.LinCore.Core.C_Kμ_144 v1
        -> coe
             C_nd_690 (coe (4 :: Integer)) (coe du_encF_832 (coe v1))
             (coe C_lf_688) (coe C_lf_688) (coe C_lf_688)
      MAlonzo.Code.Once.LinCore.Core.C__'8853'f__146 v1 v2
        -> coe
             C_nd_690 (coe (5 :: Integer)) (coe du_encF_832 (coe v1))
             (coe du_encF_832 (coe v2)) (coe C_lf_688) (coe C_lf_688)
      MAlonzo.Code.Once.LinCore.Core.C__'8855'f__148 v1 v2
        -> coe
             C_nd_690 (coe (6 :: Integer)) (coe du_encF_832 (coe v1))
             (coe du_encF_832 (coe v2)) (coe C_lf_688) (coe C_lf_688)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.TyEq.pickF
d_pickF_846 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Flat.T_Base_46 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134
d_pickF_846 ~v0 v1 v2 v3 v4 = du_pickF_846 v1 v2 v3 v4
du_pickF_846 ::
  Integer ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Flat.T_Base_46 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134
du_pickF_846 v0 v1 v2 v3
  = case coe v0 of
      0 -> coe MAlonzo.Code.Once.LinCore.Core.C_Idf_136
      1 -> coe MAlonzo.Code.Once.LinCore.Core.C_Kone_138
      2 -> coe MAlonzo.Code.Once.LinCore.Core.C_Kzero_140
      3 -> coe MAlonzo.Code.Once.LinCore.Core.C_Kb_142 (coe v3)
      4 -> coe MAlonzo.Code.Once.LinCore.Core.C_Kμ_144 (coe v1)
      5 -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8853'f__146 (coe v1) (coe v2)
      6 -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8855'f__148 (coe v1) (coe v2)
      _ -> coe MAlonzo.Code.Once.LinCore.Core.C_Idf_136
-- Once.LinCore.TyEq.decF
d_decF_896 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Tr_686 -> MAlonzo.Code.Once.LinCore.Core.T_LF_134
d_decF_896 ~v0 v1 = du_decF_896 v1
du_decF_896 :: T_Tr_686 -> MAlonzo.Code.Once.LinCore.Core.T_LF_134
du_decF_896 v0
  = case coe v0 of
      C_lf_688 -> coe MAlonzo.Code.Once.LinCore.Core.C_Idf_136
      C_nd_690 v1 v2 v3 v4 v5
        -> coe
             du_pickF_846 (coe v1) (coe du_decF_896 (coe v2))
             (coe du_decF_896 (coe v3)) (coe du_decB_812 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.TyEq.enc
d_enc_904 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> T_Tr_686
d_enc_904 ~v0 v1 = du_enc_904 v1
du_enc_904 :: MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> T_Tr_686
du_enc_904 v0
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_One_180
        -> coe du_tag_800 (coe (0 :: Integer))
      MAlonzo.Code.Once.LinCore.Core.C_Zero_182
        -> coe du_tag_800 (coe (1 :: Integer))
      MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v1 v2
        -> coe
             C_nd_690 (coe (2 :: Integer)) (coe du_enc_904 (coe v1))
             (coe du_enc_904 (coe v2)) (coe C_lf_688) (coe C_lf_688)
      MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v1 v2
        -> coe
             C_nd_690 (coe (3 :: Integer)) (coe du_enc_904 (coe v1))
             (coe du_enc_904 (coe v2)) (coe C_lf_688) (coe C_lf_688)
      MAlonzo.Code.Once.LinCore.Core.C_Ct_188 v1 v2
        -> coe
             C_nd_690 (coe (4 :: Integer)) (coe du_tag_800 (coe v1))
             (coe du_enc_904 (coe v2)) (coe C_lf_688) (coe C_lf_688)
      MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v1 v2 v3 v4
        -> coe
             C_nd_690 (coe (5 :: Integer)) (coe du_encK_816 (coe v1))
             (coe du_encG_824 (coe v2)) (coe du_enc_904 (coe v3))
             (coe du_enc_904 (coe v4))
      MAlonzo.Code.Once.LinCore.Core.C_Nu_192 v1
        -> coe
             C_nd_690 (coe (6 :: Integer)) (coe du_encF_832 (coe v1))
             (coe C_lf_688) (coe C_lf_688) (coe C_lf_688)
      MAlonzo.Code.Once.LinCore.Core.C_μt_194 v1
        -> coe
             C_nd_690 (coe (7 :: Integer)) (coe du_encF_832 (coe v1))
             (coe C_lf_688) (coe C_lf_688) (coe C_lf_688)
      MAlonzo.Code.Once.LinCore.Core.C_Bt_196 v1
        -> coe
             C_nd_690 (coe (8 :: Integer)) (coe du_encB_808 (coe v1))
             (coe C_lf_688) (coe C_lf_688) (coe C_lf_688)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.TyEq.Kids
d_Kids_932 a0 = ()
data T_Kids_932
  = C_kids_970 MAlonzo.Code.Once.LinCore.Core.T_LTy_178
               MAlonzo.Code.Once.LinCore.Core.T_LTy_178
               MAlonzo.Code.Once.LinCore.Core.T_LTy_178
               MAlonzo.Code.Once.LinCore.Core.T_LTy_178
               MAlonzo.Code.Once.LinCore.Core.T_LF_134
               MAlonzo.Code.Once.LinCore.Flat.T_Base_46
               MAlonzo.Code.Once.LinCore.Core.T_Kd_150
               MAlonzo.Code.Once.LinCore.Core.T_Gr_156 Integer
-- Once.LinCore.TyEq.Kids.t₁
d_t'8321'_952 ::
  T_Kids_932 -> MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_t'8321'_952 v0
  = case coe v0 of
      C_kids_970 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.TyEq.Kids.t₂
d_t'8322'_954 ::
  T_Kids_932 -> MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_t'8322'_954 v0
  = case coe v0 of
      C_kids_970 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.TyEq.Kids.t₃
d_t'8323'_956 ::
  T_Kids_932 -> MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_t'8323'_956 v0
  = case coe v0 of
      C_kids_970 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.TyEq.Kids.t₄
d_t'8324'_958 ::
  T_Kids_932 -> MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_t'8324'_958 v0
  = case coe v0 of
      C_kids_970 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.TyEq.Kids.f₁
d_f'8321'_960 ::
  T_Kids_932 -> MAlonzo.Code.Once.LinCore.Core.T_LF_134
d_f'8321'_960 v0
  = case coe v0 of
      C_kids_970 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.TyEq.Kids.b₁
d_b'8321'_962 ::
  T_Kids_932 -> MAlonzo.Code.Once.LinCore.Flat.T_Base_46
d_b'8321'_962 v0
  = case coe v0 of
      C_kids_970 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.TyEq.Kids.k₁
d_k'8321'_964 ::
  T_Kids_932 -> MAlonzo.Code.Once.LinCore.Core.T_Kd_150
d_k'8321'_964 v0
  = case coe v0 of
      C_kids_970 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.TyEq.Kids.g₂
d_g'8322'_966 ::
  T_Kids_932 -> MAlonzo.Code.Once.LinCore.Core.T_Gr_156
d_g'8322'_966 v0
  = case coe v0 of
      C_kids_970 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.TyEq.Kids.l₁
d_l'8321'_968 :: T_Kids_932 -> Integer
d_l'8321'_968 v0
  = case coe v0 of
      C_kids_970 v1 v2 v3 v4 v5 v6 v7 v8 v9 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.TyEq.pickT
d_pickT_972 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer -> T_Kids_932 -> MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_pickT_972 ~v0 v1 v2 = du_pickT_972 v1 v2
du_pickT_972 ::
  Integer -> T_Kids_932 -> MAlonzo.Code.Once.LinCore.Core.T_LTy_178
du_pickT_972 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Once.LinCore.Core.C_One_180
      1 -> coe MAlonzo.Code.Once.LinCore.Core.C_Zero_182
      2 -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
             (coe d_t'8321'_952 (coe v1)) (coe d_t'8322'_954 (coe v1))
      3 -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8853't__186
             (coe d_t'8321'_952 (coe v1)) (coe d_t'8322'_954 (coe v1))
      4 -> coe
             MAlonzo.Code.Once.LinCore.Core.C_Ct_188
             (coe d_l'8321'_968 (coe v1)) (coe d_t'8322'_954 (coe v1))
      5 -> coe
             MAlonzo.Code.Once.LinCore.Core.C_Fn_190
             (coe d_k'8321'_964 (coe v1)) (coe d_g'8322'_966 (coe v1))
             (coe d_t'8323'_956 (coe v1)) (coe d_t'8324'_958 (coe v1))
      6 -> coe
             MAlonzo.Code.Once.LinCore.Core.C_Nu_192
             (coe d_f'8321'_960 (coe v1))
      7 -> coe
             MAlonzo.Code.Once.LinCore.Core.C_μt_194
             (coe d_f'8321'_960 (coe v1))
      8 -> coe
             MAlonzo.Code.Once.LinCore.Core.C_Bt_196
             (coe d_b'8321'_962 (coe v1))
      _ -> coe MAlonzo.Code.Once.LinCore.Core.C_One_180
-- Once.LinCore.TyEq.dec
d_dec_994 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_Tr_686 -> MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_dec_994 ~v0 v1 = du_dec_994 v1
du_dec_994 :: T_Tr_686 -> MAlonzo.Code.Once.LinCore.Core.T_LTy_178
du_dec_994 v0
  = case coe v0 of
      C_lf_688 -> coe MAlonzo.Code.Once.LinCore.Core.C_One_180
      C_nd_690 v1 v2 v3 v4 v5
        -> coe
             du_pickT_972 (coe v1)
             (coe
                C_kids_970 (coe du_dec_994 (coe v2)) (coe du_dec_994 (coe v3))
                (coe du_dec_994 (coe v4)) (coe du_dec_994 (coe v5))
                (coe du_decF_896 (coe v2)) (coe du_decB_812 (coe v2))
                (coe du_decK_820 (coe v2)) (coe du_decG_828 (coe v3))
                (coe d_tagOf_804 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.TyEq.decB-enc
d_decB'45'enc_1008 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Flat.T_Base_46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_decB'45'enc_1008 = erased
-- Once.LinCore.TyEq.decK-enc
d_decK'45'enc_1012 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Kd_150 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_decK'45'enc_1012 = erased
-- Once.LinCore.TyEq.decG-enc
d_decG'45'enc_1016 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_decG'45'enc_1016 = erased
-- Once.LinCore.TyEq.decF-enc
d_decF'45'enc_1020 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_decF'45'enc_1020 = erased
-- Once.LinCore.TyEq.dec-enc
d_dec'45'enc_1036 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_dec'45'enc_1036 = erased
-- Once.LinCore.TyEq.eqT
d_eqT_1068 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool
d_eqT_1068 ~v0 v1 v2 = du_eqT_1068 v1 v2
du_eqT_1068 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool
du_eqT_1068 v0 v1
  = coe
      du_eqTr_692 (coe du_enc_904 (coe v0)) (coe du_enc_904 (coe v1))
-- Once.LinCore.TyEq.eqT-ok
d_eqT'45'ok_1078 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eqT'45'ok_1078 = erased
-- Once.LinCore.TyEq.eqT-refl
d_eqT'45'refl_1088 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eqT'45'refl_1088 = erased
