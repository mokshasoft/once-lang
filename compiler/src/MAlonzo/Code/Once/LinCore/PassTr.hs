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

module MAlonzo.Code.Once.LinCore.PassTr where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Once.LinCore.Core
import qualified MAlonzo.Code.Once.LinCore.Flat
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Spec.Type

-- Once.LinCore.PassTr._._∋[_]_
d__'8715''91'_'93'__10 a0 a1 a2 a3 = ()
-- Once.LinCore.PassTr._.Blk
d_Blk_30 a0 a1 a2 a3 a4 a5 = ()
-- Once.LinCore.PassTr._.Body
d_Body_32 a0 a1 a2 = ()
-- Once.LinCore.PassTr._.Cx
d_Cx_40 a0 = ()
-- Once.LinCore.PassTr._.Defs
d_Defs_42 a0 a1 = ()
-- Once.LinCore.PassTr._.Gd
d_Gd_50 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_152 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754 -> ()
d_Gd_50 = erased
-- Once.LinCore.PassTr._.Gr
d_Gr_52 a0 = ()
-- Once.LinCore.PassTr._.Kd
d_Kd_58 a0 = ()
-- Once.LinCore.PassTr._.LF
d_LF_66 a0 = ()
-- Once.LinCore.PassTr._.LF∙
d_LF'8729'_68 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_130 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174
d_LF'8729'_68 ~v0 = du_LF'8729'_68
du_LF'8729'_68 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_130 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174
du_LF'8729'_68 = coe MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_194
-- Once.LinCore.PassTr._.LTm
d_LTm_70 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 -> ()
d_LTm_70 = erased
-- Once.LinCore.PassTr._.LTy
d_LTy_72 a0 = ()
-- Once.LinCore.PassTr._.Sg
d_Sg_88 a0 = ()
-- Once.LinCore.PassTr._.Sig
d_Sig_92 a0 = ()
-- Once.LinCore.PassTr._.Tm
d_Tm_96 a0 a1 a2 a3 a4 = ()
-- Once.LinCore.PassTr._.scod
d_scod_322 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Sig_676 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
d_scod_322 ~v0 = du_scod_322
du_scod_322 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_676 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
du_scod_322 = coe MAlonzo.Code.Once.LinCore.Core.du_scod_694
-- Once.LinCore.PassTr._.sdom
d_sdom_324 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Sig_676 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
d_sdom_324 ~v0 = du_sdom_324
du_sdom_324 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_676 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
du_sdom_324 = coe MAlonzo.Code.Once.LinCore.Core.du_sdom_692
-- Once.LinCore.PassTr._.⌜_⌝
d_'8988'_'8989'_354 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174
d_'8988'_'8989'_354 ~v0 = du_'8988'_'8989'_354
du_'8988'_'8989'_354 ::
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174
du_'8988'_'8989'_354
  = coe MAlonzo.Code.Once.LinCore.Core.du_'8988'_'8989'_528
-- Once.LinCore.PassTr._.Sg.cod
d_cod_530 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_700 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174
d_cod_530 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_cod_720 (coe v0)
-- Once.LinCore.PassTr._.Sg.dom
d_dom_532 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_700 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174
d_dom_532 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_dom_718 (coe v0)
-- Once.LinCore.PassTr._.Sg.env
d_env_534 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_700 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174
d_env_534 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_env_716 (coe v0)
-- Once.LinCore.PassTr._.Sg.gr
d_gr_536 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_700 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_152
d_gr_536 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_gr_714 (coe v0)
-- Once.LinCore.PassTr._.Sg.kd
d_kd_538 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_700 ->
  MAlonzo.Code.Once.LinCore.Core.T_Kd_146
d_kd_538 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_kd_712 (coe v0)
-- Once.LinCore.PassTr._.Sig.info
d_info_542 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_676 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_info_542 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_info_688 (coe v0)
-- Once.LinCore.PassTr._.Sig.sA
d_sA_544 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_676 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_sA_544 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_sA_684 (coe v0)
-- Once.LinCore.PassTr._.Sig.sB
d_sB_546 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_676 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_sB_546 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_sB_686 (coe v0)
-- Once.LinCore.PassTr._.Flat.Lit
d_Lit_652 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> ()
d_Lit_652 = erased
-- Once.LinCore.PassTr._.IR
d_IR_746 a0 a1 a2 a3 = ()
data T_IR_746
  = C_id_762 |
    C__'8728'__770 MAlonzo.Code.Once.LinCore.Core.T_LTy_174 T_IR_746
                   T_IR_746 |
    C_'10216'_'44'_'10217'_778 T_IR_746 T_IR_746 | C_fst_784 |
    C_snd_790 | C_inl_796 | C_inr_802 | C_case_810 T_IR_746 T_IR_746 |
    C_terminal_814 | C_initial_818 | C_curry_830 T_IR_746 AgdaAny |
    C_apply_838 | C_In_842 | C_out'45'μ_846 | C_Cata_854 T_IR_746 |
    C_Ana_864 T_IR_746 T_BlkIR_752 | C_Out_868 | C_in'45'ν_872 |
    C_Iter_882 T_IR_746 T_BlkIR_752 | C_const_886 AgdaAny |
    C_SigOp_890 MAlonzo.Code.Once.LinCore.Core.T_Sig_676 |
    C_Call_900 Integer MAlonzo.Code.Once.LinCore.Core.T_Gr_152
               MAlonzo.Code.Once.LinCore.Core.T__'8715''91'_'93'__734
-- Once.LinCore.PassTr._.BlkIR
d_BlkIR_752 a0 a1 a2 a3 a4 = ()
data T_BlkIR_752
  = C_i'45'id_904 | C_i'45''8728'_916 T_BlkIR_752 T_BlkIR_752 |
    C_i'45'pair_928 T_BlkIR_752 T_BlkIR_752 | C_i'45'fst_934 |
    C_i'45'snd_940 | C_i'45'inl_946 | C_i'45'inr_952 |
    C_i'45'case_964 T_BlkIR_752 T_BlkIR_752 | C_i'45'term_968 |
    C_i'45'init_972 | C_i'45'curry_986 | C_i'45'apply_992 |
    C_i'45'In_996 | C_i'45'out_1000 | C_i'45'cata_1010 T_BlkIR_752 |
    C_i'45'ana_1022 | C_i'45'Out_1026 | C_i'45'inν_1030 |
    C_i'45'const_1036 | C_i'45'op_1040 | C_i'45'call_1050
-- Once.LinCore.PassTr._.GdIR
d_GdIR_758 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_152 -> T_IR_746 -> ()
d_GdIR_758 = erased
-- Once.LinCore.PassTr.dropl
d_dropl_1064 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754
d_dropl_1064 ~v0 ~v1 ~v2 v3 = du_dropl_1064 v3
du_dropl_1064 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754
du_dropl_1064 v0
  = coe
      MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
      (coe
         MAlonzo.Code.Once.LinCore.Core.C__'8855't__180
         (coe MAlonzo.Code.Once.LinCore.Core.C_One_176) (coe v0))
      (coe MAlonzo.Code.Once.LinCore.Core.C_lul_822)
      (coe
         MAlonzo.Code.Once.LinCore.Core.C__'8855'l__804
         (coe MAlonzo.Code.Once.LinCore.Core.C_drop_868)
         (coe MAlonzo.Code.Once.LinCore.Core.C_lid_782))
-- Once.LinCore.PassTr.k-dropl
d_k'45'dropl_1074 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_764
d_k'45'dropl_1074 ~v0 ~v1 ~v2 ~v3 = du_k'45'dropl_1074
du_k'45'dropl_1074 :: MAlonzo.Code.Once.LinCore.Core.T_Blk_764
du_k'45'dropl_1074
  = coe
      MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
      (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1162)
      (coe
         MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1144
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1208)
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1114))
-- Once.LinCore.PassTr.withE
d_withE_1084 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754
d_withE_1084 ~v0 v1 v2 ~v3 v4 = du_withE_1084 v1 v2 v4
du_withE_1084 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754
du_withE_1084 v0 v1 v2
  = coe
      MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
      (coe
         MAlonzo.Code.Once.LinCore.Core.C__'8855't__180 (coe v0) (coe v1))
      (coe MAlonzo.Code.Once.LinCore.Core.C_blift_970 v2)
      (coe
         MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
         (coe
            MAlonzo.Code.Once.LinCore.Core.C__'8855't__180
            (coe MAlonzo.Code.Once.LinCore.Core.C_One_176) (coe v1))
         (coe
            MAlonzo.Code.Once.LinCore.Core.C__'8855'l__804
            (coe
               MAlonzo.Code.Once.LinCore.Core.C_bsnd_990
               (coe MAlonzo.Code.Once.LinCore.Core.C_bcopy_1012))
            (coe MAlonzo.Code.Once.LinCore.Core.C_lid_782))
         (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_828))
-- Once.LinCore.PassTr.k-withE
d_k'45'withE_1098 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_764 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_764
d_k'45'withE_1098 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_k'45'withE_1098 v5
du_k'45'withE_1098 ::
  MAlonzo.Code.Once.LinCore.Core.T_Blk_764 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_764
du_k'45'withE_1098 v0
  = coe
      MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
      (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lift_1322 v0)
      (coe
         MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
         (coe
            MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1144
            (coe
               MAlonzo.Code.Once.LinCore.Core.C_k'45'snd_1346
               (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'copy_1374))
            (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1114))
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1168))
-- Once.LinCore.PassTr.copyIn
d_copyIn_1110 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754
d_copyIn_1110 ~v0 v1 v2 ~v3 v4 = du_copyIn_1110 v1 v2 v4
du_copyIn_1110 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754
du_copyIn_1110 v0 v1 v2
  = coe
      MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
      (coe
         MAlonzo.Code.Once.LinCore.Core.C__'8855't__180 (coe v0) (coe v1))
      (coe MAlonzo.Code.Once.LinCore.Core.C_blift_970 v2)
      (coe
         MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
         (coe
            MAlonzo.Code.Once.LinCore.Core.C__'8855't__180
            (coe MAlonzo.Code.Once.LinCore.Core.C_One_176) (coe v1))
         (coe
            MAlonzo.Code.Once.LinCore.Core.C__'8855'l__804
            (coe MAlonzo.Code.Once.LinCore.Core.C_bcopy_1012)
            (coe MAlonzo.Code.Once.LinCore.Core.C_lid_782))
         (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_828))
-- Once.LinCore.PassTr.k-copyIn
d_k'45'copyIn_1124 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_764 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_764
d_k'45'copyIn_1124 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_k'45'copyIn_1124 v5
du_k'45'copyIn_1124 ::
  MAlonzo.Code.Once.LinCore.Core.T_Blk_764 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_764
du_k'45'copyIn_1124 v0
  = coe
      MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
      (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lift_1322 v0)
      (coe
         MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
         (coe
            MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1144
            (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'copy_1374)
            (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1114))
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1168))
-- Once.LinCore.PassTr.mapL
d_mapL_1138 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_130 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754
d_mapL_1138 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_mapL_1138 v4 v5 v6
du_mapL_1138 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_130 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754
du_mapL_1138 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.LinCore.Core.C_Idf_132 -> coe v2
      MAlonzo.Code.Once.LinCore.Core.C_Kone_134
        -> coe MAlonzo.Code.Once.LinCore.Core.C_lid_782
      MAlonzo.Code.Once.LinCore.Core.C_Kzero_136
        -> coe MAlonzo.Code.Once.LinCore.Core.C_lid_782
      MAlonzo.Code.Once.LinCore.Core.C_Kb_138 v3
        -> coe MAlonzo.Code.Once.LinCore.Core.C_lid_782
      MAlonzo.Code.Once.LinCore.Core.C_Kμ_140 v3
        -> coe MAlonzo.Code.Once.LinCore.Core.C_lid_782
      MAlonzo.Code.Once.LinCore.Core.C__'8853'f__142 v3 v4
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_lcase_894
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                (coe
                   MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_194 (coe v3) (coe v0))
                (coe MAlonzo.Code.Once.LinCore.Core.C_linl_876)
                (coe du_mapL_1138 (coe v0) (coe v3) (coe v2)))
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                (coe
                   MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_194 (coe v4) (coe v0))
                (coe MAlonzo.Code.Once.LinCore.Core.C_linr_884)
                (coe du_mapL_1138 (coe v0) (coe v4) (coe v2)))
      MAlonzo.Code.Once.LinCore.Core.C__'8855'f__144 v3 v4
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8855'l__804
             (coe du_mapL_1138 (coe v0) (coe v3) (coe v2))
             (coe du_mapL_1138 (coe v0) (coe v4) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.PassTr.k-mapL
d_k'45'mapL_1178 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_130 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_764 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_764
d_k'45'mapL_1178 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7
  = du_k'45'mapL_1178 v5 v7
du_k'45'mapL_1178 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_130 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_764 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_764
du_k'45'mapL_1178 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_Idf_132 -> coe v1
      MAlonzo.Code.Once.LinCore.Core.C_Kone_134
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1114
      MAlonzo.Code.Once.LinCore.Core.C_Kzero_136
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1114
      MAlonzo.Code.Once.LinCore.Core.C_Kb_138 v2
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1114
      MAlonzo.Code.Once.LinCore.Core.C_Kμ_140 v2
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1114
      MAlonzo.Code.Once.LinCore.Core.C__'8853'f__142 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45'case_1238
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inl_1216)
                (coe du_k'45'mapL_1178 (coe v2) (coe v1)))
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inr_1224)
                (coe du_k'45'mapL_1178 (coe v3) (coe v1)))
      MAlonzo.Code.Once.LinCore.Core.C__'8855'f__144 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1144
             (coe du_k'45'mapL_1178 (coe v2) (coe v1))
             (coe du_k'45'mapL_1178 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.PassTr.InS
d_InS_1206 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_130 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174
d_InS_1206 ~v0 v1 = du_InS_1206 v1
du_InS_1206 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_130 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174
du_InS_1206 v0
  = coe
      MAlonzo.Code.Once.LinCore.Core.C__'8853't__182
      (coe
         MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_194 (coe v0)
         (coe MAlonzo.Code.Once.LinCore.Core.C_Nu_188 (coe v0)))
      (coe MAlonzo.Code.Once.LinCore.Core.C_Nu_188 (coe v0))
-- Once.LinCore.PassTr.inco
d_inco_1214 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_130 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754
d_inco_1214 ~v0 ~v1 v2 = du_inco_1214 v2
du_inco_1214 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_130 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754
du_inco_1214 v0
  = coe
      MAlonzo.Code.Once.LinCore.Core.C_lcase_894
      (coe
         du_mapL_1138 (coe du_InS_1206 (coe v0)) (coe v0)
         (coe MAlonzo.Code.Once.LinCore.Core.C_linr_884))
      (coe
         MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
         (coe
            MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_194 (coe v0)
            (coe MAlonzo.Code.Once.LinCore.Core.C_Nu_188 (coe v0)))
         (coe
            du_mapL_1138 (coe du_InS_1206 (coe v0)) (coe v0)
            (coe MAlonzo.Code.Once.LinCore.Core.C_linr_884))
         (coe MAlonzo.Code.Once.LinCore.Core.C_lout_1084))
-- Once.LinCore.PassTr.k-inco
d_k'45'inco_1222 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_130 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_764
d_k'45'inco_1222 ~v0 ~v1 v2 = du_k'45'inco_1222 v2
du_k'45'inco_1222 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_130 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_764
du_k'45'inco_1222 v0
  = coe
      MAlonzo.Code.Once.LinCore.Core.C_k'45'case_1238
      (coe
         du_k'45'mapL_1178 (coe v0)
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inr_1224))
      (coe
         MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
         (coe
            du_k'45'mapL_1178 (coe v0)
            (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inr_1224))
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'nout_1446))
-- Once.LinCore.PassTr.tr
d_tr_1232 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  T_IR_746 -> MAlonzo.Code.Once.LinCore.Core.T_Tm_754
d_tr_1232 ~v0 ~v1 v2 v3 v4 = du_tr_1232 v2 v3 v4
du_tr_1232 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  T_IR_746 -> MAlonzo.Code.Once.LinCore.Core.T_Tm_754
du_tr_1232 v0 v1 v2
  = case coe v2 of
      C_id_762 -> coe MAlonzo.Code.Once.LinCore.Core.C_lid_782
      C__'8728'__770 v4 v6 v7
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792 v4
             (coe du_tr_1232 (coe v4) (coe v1) (coe v6))
             (coe du_tr_1232 (coe v0) (coe v4) (coe v7))
      C_'10216'_'44'_'10217'_778 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__180 v8 v9
               -> coe
                    MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                    (coe
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__180 (coe v0) (coe v0))
                    (coe
                       MAlonzo.Code.Once.LinCore.Core.C__'8855'l__804
                       (coe du_tr_1232 (coe v0) (coe v8) (coe v6))
                       (coe du_tr_1232 (coe v0) (coe v9) (coe v7)))
                    (coe MAlonzo.Code.Once.LinCore.Core.C_dup_862)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fst_784
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__180 (coe v1)
                (coe MAlonzo.Code.Once.LinCore.Core.C_One_176))
             (coe MAlonzo.Code.Once.LinCore.Core.C_ρl_810)
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'8855'l__804
                (coe MAlonzo.Code.Once.LinCore.Core.C_lid_782)
                (coe MAlonzo.Code.Once.LinCore.Core.C_drop_868))
      C_snd_790
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__180
                (coe MAlonzo.Code.Once.LinCore.Core.C_One_176) (coe v1))
             (coe MAlonzo.Code.Once.LinCore.Core.C_lul_822)
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'8855'l__804
                (coe MAlonzo.Code.Once.LinCore.Core.C_drop_868)
                (coe MAlonzo.Code.Once.LinCore.Core.C_lid_782))
      C_inl_796 -> coe MAlonzo.Code.Once.LinCore.Core.C_linl_876
      C_inr_802 -> coe MAlonzo.Code.Once.LinCore.Core.C_linr_884
      C_case_810 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8853't__182 v8 v9
               -> coe
                    MAlonzo.Code.Once.LinCore.Core.C_lcase_894
                    (coe du_tr_1232 (coe v8) (coe v1) (coe v6))
                    (coe du_tr_1232 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_terminal_814 -> coe MAlonzo.Code.Once.LinCore.Core.C_drop_868
      C_initial_818 -> coe MAlonzo.Code.Once.LinCore.Core.C_lzero_900
      C_curry_830 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C_Fn_186 v9 v10 v11 v12
               -> coe
                    MAlonzo.Code.Once.LinCore.Core.C_llamω_1052
                    (coe
                       MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C__'8855't__180 (coe v0) (coe v11))
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C_blift_970
                          (coe
                             du_tr_1232
                             (coe
                                MAlonzo.Code.Once.LinCore.Core.C__'8855't__180 (coe v0) (coe v11))
                             (coe v12) (coe v7)))
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.C__'8855't__180
                             (coe MAlonzo.Code.Once.LinCore.Core.C_One_176) (coe v11))
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.C__'8855'l__804
                             (coe MAlonzo.Code.Once.LinCore.Core.C_bcopy_1012)
                             (coe MAlonzo.Code.Once.LinCore.Core.C_lid_782))
                          (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_828)))
                    (coe
                       du_tr'45'gd_1256 (coe v10) (coe v0) (coe v11) (coe v12) (coe v7)
                       (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_apply_838
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__180 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.LinCore.Core.C_Fn_186 v8 v9 v10 v11
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C__'8855't__180
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C_Fn_186
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_many_150) (coe v9) (coe v10)
                                 (coe v1))
                              (coe v1))
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855't__180
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_One_176) (coe v1))
                              (coe MAlonzo.Code.Once.LinCore.Core.C_lul_822)
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855'l__804
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_drop_868)
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_lid_782)))
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C_lend_962
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C_bsnd_990
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_bev_1070)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_In_842 -> coe MAlonzo.Code.Once.LinCore.Core.C_lIn_906
      C_out'45'μ_846 -> coe MAlonzo.Code.Once.LinCore.Core.C_lOutμ_912
      C_Cata_854 v6
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__180 v7 v8
               -> case coe v8 of
                    MAlonzo.Code.Once.LinCore.Core.C_μt_190 v9
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C__'8855't__180 (coe v7) (coe v1))
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855't__180
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_One_176) (coe v1))
                              (coe MAlonzo.Code.Once.LinCore.Core.C_lul_822)
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855'l__804
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_drop_868)
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_lid_782)))
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C_lend_962
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C_lcata_920
                                 (coe
                                    MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                                    (coe
                                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__180 (coe v7)
                                       (coe
                                          MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_194 (coe v9)
                                          (coe v1)))
                                    (coe
                                       MAlonzo.Code.Once.LinCore.Core.C_blift_970
                                       (coe
                                          du_tr_1232
                                          (coe
                                             MAlonzo.Code.Once.LinCore.Core.C__'8855't__180 (coe v7)
                                             (coe
                                                MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_194
                                                (coe v9) (coe v1)))
                                          (coe v1) (coe v6)))
                                    (coe
                                       MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                                       (coe
                                          MAlonzo.Code.Once.LinCore.Core.C__'8855't__180
                                          (coe MAlonzo.Code.Once.LinCore.Core.C_One_176)
                                          (coe
                                             MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_194 (coe v9)
                                             (coe v1)))
                                       (coe
                                          MAlonzo.Code.Once.LinCore.Core.C__'8855'l__804
                                          (coe
                                             MAlonzo.Code.Once.LinCore.Core.C_bsnd_990
                                             (coe MAlonzo.Code.Once.LinCore.Core.C_bcopy_1012))
                                          (coe MAlonzo.Code.Once.LinCore.Core.C_lid_782))
                                       (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_828)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Ana_864 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__180 v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.LinCore.Core.C_Nu_188 v10
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C__'8855't__180
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C_Fn_186
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_many_150)
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_act_154) (coe v9)
                                 (coe
                                    MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_194 (coe v10)
                                    (coe v9)))
                              (coe v9))
                           (coe MAlonzo.Code.Once.LinCore.Core.C_lunf_1078)
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C__'8855'l__804
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C_llamω_1052
                                 (coe
                                    MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792 v0
                                    (coe
                                       MAlonzo.Code.Once.LinCore.Core.C_blift_970
                                       (coe
                                          du_tr_1232 (coe v0)
                                          (coe
                                             MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_194
                                             (coe v10) (coe v9))
                                          (coe v6)))
                                    (coe
                                       MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                                       (coe
                                          MAlonzo.Code.Once.LinCore.Core.C__'8855't__180
                                          (coe MAlonzo.Code.Once.LinCore.Core.C_One_176) (coe v9))
                                       (coe
                                          MAlonzo.Code.Once.LinCore.Core.C__'8855'l__804
                                          (coe MAlonzo.Code.Once.LinCore.Core.C_bcopy_1012)
                                          (coe MAlonzo.Code.Once.LinCore.Core.C_lid_782))
                                       (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_828)))
                                 (coe
                                    MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
                                    (coe
                                       MAlonzo.Code.Once.LinCore.Core.C_k'45'lift_1322
                                       (coe
                                          du_tr'45'blk_1242 (coe v0)
                                          (coe
                                             MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_194
                                             (coe v10) (coe v9))
                                          (coe v6) (coe v7)))
                                    (coe
                                       MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
                                       (coe
                                          MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1144
                                          (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'copy_1374)
                                          (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1114))
                                       (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1168))))
                              (coe MAlonzo.Code.Once.LinCore.Core.C_lid_782))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Out_868 -> coe MAlonzo.Code.Once.LinCore.Core.C_lout_1084
      C_in'45'ν_872
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C_Nu_188 v4
               -> coe
                    MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                    (coe
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__180
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C_Fn_186
                          (coe MAlonzo.Code.Once.LinCore.Core.C_many_150)
                          (coe MAlonzo.Code.Once.LinCore.Core.C_act_154)
                          (coe du_InS_1206 (coe v4))
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_194 (coe v4)
                             (coe du_InS_1206 (coe v4))))
                       (coe du_InS_1206 (coe v4)))
                    (coe MAlonzo.Code.Once.LinCore.Core.C_lunf_1078)
                    (coe
                       MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C__'8855't__180
                          (coe MAlonzo.Code.Once.LinCore.Core.C_One_176)
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_194 (coe v4) (coe v1)))
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C__'8855'l__804
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.C_llamω_1052
                             (coe du_inco_1214 (coe v4)) (coe du_k'45'inco_1222 (coe v4)))
                          (coe MAlonzo.Code.Once.LinCore.Core.C_linl_876))
                       (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_828))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Iter_882 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__180 v8 v9
               -> coe
                    MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                    (coe
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__180 (coe v8) (coe v1))
                    (coe
                       MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C__'8855't__180
                          (coe MAlonzo.Code.Once.LinCore.Core.C_One_176) (coe v1))
                       (coe MAlonzo.Code.Once.LinCore.Core.C_lul_822)
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C__'8855'l__804
                          (coe MAlonzo.Code.Once.LinCore.Core.C_drop_868)
                          (coe MAlonzo.Code.Once.LinCore.Core.C_lid_782)))
                    (coe
                       MAlonzo.Code.Once.LinCore.Core.C_lend_962
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C_liter_1106
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792 v0
                             (coe
                                MAlonzo.Code.Once.LinCore.Core.C_blift_970
                                (coe
                                   du_tr_1232 (coe v0)
                                   (coe
                                      MAlonzo.Code.Once.LinCore.Core.C__'8853't__182 (coe v1)
                                      (coe v9))
                                   (coe v6)))
                             (coe
                                MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                                (coe
                                   MAlonzo.Code.Once.LinCore.Core.C__'8855't__180
                                   (coe MAlonzo.Code.Once.LinCore.Core.C_One_176) (coe v9))
                                (coe
                                   MAlonzo.Code.Once.LinCore.Core.C__'8855'l__804
                                   (coe
                                      MAlonzo.Code.Once.LinCore.Core.C_bsnd_990
                                      (coe MAlonzo.Code.Once.LinCore.Core.C_bcopy_1012))
                                   (coe MAlonzo.Code.Once.LinCore.Core.C_lid_782))
                                (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_828)))
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
                             (coe
                                MAlonzo.Code.Once.LinCore.Core.C_k'45'lift_1322
                                (coe
                                   du_tr'45'blk_1242 (coe v0)
                                   (coe
                                      MAlonzo.Code.Once.LinCore.Core.C__'8853't__182 (coe v1)
                                      (coe v9))
                                   (coe v6) (coe v7)))
                             (coe
                                MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
                                (coe
                                   MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1144
                                   (coe
                                      MAlonzo.Code.Once.LinCore.Core.C_k'45'snd_1346
                                      (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'copy_1374))
                                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1114))
                                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1168)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_const_886 v4
        -> coe MAlonzo.Code.Once.LinCore.Core.C_lconst_1090 v4
      C_SigOp_890 v3 -> coe MAlonzo.Code.Once.LinCore.Core.C_lop_1096 v3
      C_Call_900 v3 v4 v7
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__180
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_Ct_184 (coe v3)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_One_176))
                (coe v0))
             (coe MAlonzo.Code.Once.LinCore.Core.C_lapp_952 v4 v7)
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C__'8855't__180
                   (coe
                      MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_194
                      (coe MAlonzo.Code.Once.LinCore.Core.C_Idf_132)
                      (coe MAlonzo.Code.Once.LinCore.Core.C_One_176))
                   (coe v0))
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C__'8855'l__804
                   (coe
                      MAlonzo.Code.Once.LinCore.Core.C_lclo_938
                      (coe MAlonzo.Code.Once.LinCore.Core.C_Idf_132) v3
                      (coe MAlonzo.Code.Once.LinCore.Core.C_once_148) v4
                      (coe MAlonzo.Code.Once.LinCore.Core.C_One_176) v0 v1 v7)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_lid_782))
                (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_828))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.PassTr.tr-blk
d_tr'45'blk_1242 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  T_IR_746 -> T_BlkIR_752 -> MAlonzo.Code.Once.LinCore.Core.T_Blk_764
d_tr'45'blk_1242 ~v0 ~v1 v2 v3 v4 v5
  = du_tr'45'blk_1242 v2 v3 v4 v5
du_tr'45'blk_1242 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  T_IR_746 -> T_BlkIR_752 -> MAlonzo.Code.Once.LinCore.Core.T_Blk_764
du_tr'45'blk_1242 v0 v1 v2 v3
  = case coe v3 of
      C_i'45'id_904 -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1114
      C_i'45''8728'_916 v9 v10
        -> case coe v2 of
             C__'8728'__770 v12 v14 v15
               -> coe
                    MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
                    (coe du_tr'45'blk_1242 (coe v12) (coe v1) (coe v14) (coe v9))
                    (coe du_tr'45'blk_1242 (coe v0) (coe v12) (coe v15) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_i'45'pair_928 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__180 v11 v12
               -> case coe v2 of
                    C_'10216'_'44'_'10217'_778 v16 v17
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1144
                              (coe du_tr'45'blk_1242 (coe v0) (coe v11) (coe v16) (coe v9))
                              (coe du_tr'45'blk_1242 (coe v0) (coe v12) (coe v17) (coe v10)))
                           (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'dup_1202)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_i'45'fst_934
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'ρ_1150)
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1144
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1114)
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1208))
      C_i'45'snd_940
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1162)
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1144
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1208)
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1114))
      C_i'45'inl_946
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inl_1216
      C_i'45'inr_952
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inr_1224
      C_i'45'case_964 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8853't__182 v11 v12
               -> case coe v2 of
                    C_case_810 v16 v17
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C_k'45'case_1238
                           (coe du_tr'45'blk_1242 (coe v11) (coe v1) (coe v16) (coe v9))
                           (coe du_tr'45'blk_1242 (coe v12) (coe v1) (coe v17) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_i'45'term_968
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1208
      C_i'45'init_972
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'zero_1244
      C_i'45'curry_986
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lamω_1418
      C_i'45'apply_992
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1162)
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1144
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1208)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1114)))
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45'lend_1312
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_k'45'snd_1346
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'bev_1432)))
      C_i'45'In_996 -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'in_1250
      C_i'45'out_1000
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'out_1256
      C_i'45'cata_1010 v8
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__180 v9 v10
               -> case coe v10 of
                    MAlonzo.Code.Once.LinCore.Core.C_μt_190 v11
                      -> case coe v2 of
                           C_Cata_854 v15
                             -> coe
                                  MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
                                  (coe
                                     MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
                                     (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1162)
                                     (coe
                                        MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1144
                                        (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1208)
                                        (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1114)))
                                  (coe
                                     MAlonzo.Code.Once.LinCore.Core.C_k'45'lend_1312
                                     (coe
                                        MAlonzo.Code.Once.LinCore.Core.C_k'45'cata_1266
                                        (coe
                                           MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
                                           (coe
                                              MAlonzo.Code.Once.LinCore.Core.C_k'45'lift_1322
                                              (coe
                                                 du_tr'45'blk_1242
                                                 (coe
                                                    MAlonzo.Code.Once.LinCore.Core.C__'8855't__180
                                                    (coe v9)
                                                    (coe
                                                       MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_194
                                                       (coe v11) (coe v1)))
                                                 (coe v1) (coe v15) (coe v8)))
                                           (coe
                                              MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
                                              (coe
                                                 MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1144
                                                 (coe
                                                    MAlonzo.Code.Once.LinCore.Core.C_k'45'snd_1346
                                                    (coe
                                                       MAlonzo.Code.Once.LinCore.Core.C_k'45'copy_1374))
                                                 (coe
                                                    MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1114))
                                              (coe
                                                 MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1168)))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_i'45'ana_1022
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'unf_1440)
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1144
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lamω_1418)
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1114))
      C_i'45'Out_1026
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'nout_1446
      C_i'45'inν_1030
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'unf_1440)
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1144
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lamω_1418)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inl_1216))
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1168))
      C_i'45'const_1036
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'const_1454
      C_i'45'op_1040 -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'op_1460
      C_i'45'call_1050
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'app_1300)
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1144
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'clo_1286)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1114))
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1168))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.PassTr.tr-gd
d_tr'45'gd_1256 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_152 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  T_IR_746 -> AgdaAny -> AgdaAny
d_tr'45'gd_1256 ~v0 v1 ~v2 v3 v4 v5 v6 v7
  = du_tr'45'gd_1256 v1 v3 v4 v5 v6 v7
du_tr'45'gd_1256 ::
  MAlonzo.Code.Once.LinCore.Core.T_Gr_152 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  T_IR_746 -> AgdaAny -> AgdaAny
du_tr'45'gd_1256 v0 v1 v2 v3 v4 v5
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_act_154
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45'lift_1322
                (coe
                   du_tr'45'blk_1242
                   (coe
                      MAlonzo.Code.Once.LinCore.Core.C__'8855't__180 (coe v1) (coe v2))
                   (coe v3) (coe v4) (coe v5)))
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1144
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'copy_1374)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1114))
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1168))
      MAlonzo.Code.Once.LinCore.Core.C_eff_156
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.PassTr.Prog
d_Prog_1320 a0 a1 = ()
data T_Prog_1320
  = C_ε_1322 | C__'9657'_'8739'__1334 T_Prog_1320 T_IR_746 AgdaAny
-- Once.LinCore.PassTr.tr-def
d_tr'45'def_1346 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_152 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  T_IR_746 -> AgdaAny -> AgdaAny
d_tr'45'def_1346 ~v0 v1 ~v2 v3 v4 v5 v6
  = du_tr'45'def_1346 v1 v3 v4 v5 v6
du_tr'45'def_1346 ::
  MAlonzo.Code.Once.LinCore.Core.T_Gr_152 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  T_IR_746 -> AgdaAny -> AgdaAny
du_tr'45'def_1346 v0 v1 v2 v3 v4
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_act_154
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
             (coe du_tr'45'blk_1242 (coe v1) (coe v2) (coe v3) (coe v4))
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1162)
      MAlonzo.Code.Once.LinCore.Core.C_eff_156
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.PassTr.trP
d_trP_1352 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  T_Prog_1320 -> MAlonzo.Code.Once.LinCore.Core.T_Defs_1678
d_trP_1352 ~v0 v1 v2 = du_trP_1352 v1 v2
du_trP_1352 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  T_Prog_1320 -> MAlonzo.Code.Once.LinCore.Core.T_Defs_1678
du_trP_1352 v0 v1
  = case coe v1 of
      C_ε_1322 -> coe MAlonzo.Code.Once.LinCore.Core.C_ε_1680
      C__'9657'_'8739'__1334 v6 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'9656'__728 v9 v10
               -> case coe v10 of
                    MAlonzo.Code.Once.LinCore.Core.C_sg_722 v11 v12 v13 v14 v15
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C__'9656'__1686
                           (coe du_trP_1352 (coe v9) (coe v6))
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C_b1_1664
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792 v14
                                 (coe du_tr_1232 (coe v14) (coe v15) (coe v7))
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_lul_822))
                              (coe
                                 du_tr'45'def_1346 (coe v12) (coe v14) (coe v15) (coe v7) (coe v8)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
