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
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 -> ()
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
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_LF'8729'_68 ~v0 = du_LF'8729'_68
du_LF'8729'_68 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
du_LF'8729'_68 = coe MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198
-- Once.LinCore.PassTr._.LTm
d_LTm_70 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> ()
d_LTm_70 = erased
-- Once.LinCore.PassTr._.LTy
d_LTy_72 a0 = ()
-- Once.LinCore.PassTr._.Sg
d_Sg_90 a0 = ()
-- Once.LinCore.PassTr._.Sig
d_Sig_94 a0 = ()
-- Once.LinCore.PassTr._.Tm
d_Tm_98 a0 a1 a2 a3 a4 = ()
-- Once.LinCore.PassTr._.scod
d_scod_356 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
d_scod_356 ~v0 = du_scod_356
du_scod_356 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
du_scod_356 = coe MAlonzo.Code.Once.LinCore.Core.du_scod_698
-- Once.LinCore.PassTr._.sdom
d_sdom_358 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
d_sdom_358 ~v0 = du_sdom_358
du_sdom_358 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
du_sdom_358 = coe MAlonzo.Code.Once.LinCore.Core.du_sdom_696
-- Once.LinCore.PassTr._.⌜_⌝
d_'8988'_'8989'_388 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_'8988'_'8989'_388 ~v0 = du_'8988'_'8989'_388
du_'8988'_'8989'_388 ::
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
du_'8988'_'8989'_388
  = coe MAlonzo.Code.Once.LinCore.Core.du_'8988'_'8989'_532
-- Once.LinCore.PassTr._.Sg.cod
d_cod_584 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_cod_584 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_cod_724 (coe v0)
-- Once.LinCore.PassTr._.Sg.dom
d_dom_586 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_dom_586 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_dom_722 (coe v0)
-- Once.LinCore.PassTr._.Sg.env
d_env_588 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_env_588 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_env_720 (coe v0)
-- Once.LinCore.PassTr._.Sg.gr
d_gr_590 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156
d_gr_590 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_gr_718 (coe v0)
-- Once.LinCore.PassTr._.Sg.kd
d_kd_592 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Kd_150
d_kd_592 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_kd_716 (coe v0)
-- Once.LinCore.PassTr._.Sig.info
d_info_596 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_info_596 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_info_692 (coe v0)
-- Once.LinCore.PassTr._.Sig.sA
d_sA_598 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_sA_598 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_sA_688 (coe v0)
-- Once.LinCore.PassTr._.Sig.sB
d_sB_600 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_sB_600 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_sB_690 (coe v0)
-- Once.LinCore.PassTr._.IR
d_IR_692 a0 a1 a2 a3 = ()
data T_IR_692
  = C_id_708 |
    C__'8728'__716 MAlonzo.Code.Once.LinCore.Core.T_LTy_178 T_IR_692
                   T_IR_692 |
    C_'10216'_'44'_'10217'_724 T_IR_692 T_IR_692 | C_fst_730 |
    C_snd_736 | C_inl_742 | C_inr_748 | C_case_756 T_IR_692 T_IR_692 |
    C_terminal_760 | C_initial_764 | C_curry_776 T_IR_692 AgdaAny |
    C_apply_784 | C_In_788 | C_out'45'μ_792 | C_Cata_800 T_IR_692 |
    C_Ana_810 T_IR_692 T_BlkIR_698 | C_Out_814 | C_in'45'ν_818 |
    C_Iter_828 T_IR_692 T_BlkIR_698 | C_const_832 AgdaAny |
    C_SigOp_836 MAlonzo.Code.Once.LinCore.Core.T_Sig_680 |
    C_Call_846 Integer MAlonzo.Code.Once.LinCore.Core.T_Gr_156
               MAlonzo.Code.Once.LinCore.Core.T__'8715''91'_'93'__738
-- Once.LinCore.PassTr._.BlkIR
d_BlkIR_698 a0 a1 a2 a3 a4 = ()
data T_BlkIR_698
  = C_i'45'id_850 | C_i'45''8728'_862 T_BlkIR_698 T_BlkIR_698 |
    C_i'45'pair_874 T_BlkIR_698 T_BlkIR_698 | C_i'45'fst_880 |
    C_i'45'snd_886 | C_i'45'inl_892 | C_i'45'inr_898 |
    C_i'45'case_910 T_BlkIR_698 T_BlkIR_698 | C_i'45'term_914 |
    C_i'45'init_918 | C_i'45'curry_932 | C_i'45'apply_938 |
    C_i'45'In_942 | C_i'45'out_946 | C_i'45'cata_956 T_BlkIR_698 |
    C_i'45'ana_968 | C_i'45'Out_972 | C_i'45'inν_976 |
    C_i'45'const_982 | C_i'45'op_986 | C_i'45'call_996
-- Once.LinCore.PassTr._.GdIR
d_GdIR_704 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 -> T_IR_692 -> ()
d_GdIR_704 = erased
-- Once.LinCore.PassTr.dropl
d_dropl_1010 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_dropl_1010 ~v0 ~v1 ~v2 v3 = du_dropl_1010 v3
du_dropl_1010 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_dropl_1010 v0
  = coe
      MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
      (coe
         MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
         (coe MAlonzo.Code.Once.LinCore.Core.C_One_180) (coe v0))
      (coe MAlonzo.Code.Once.LinCore.Core.C_lul_826)
      (coe
         MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808
         (coe MAlonzo.Code.Once.LinCore.Core.C_drop_872)
         (coe MAlonzo.Code.Once.LinCore.Core.C_lid_786))
-- Once.LinCore.PassTr.k-dropl
d_k'45'dropl_1020 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'dropl_1020 ~v0 ~v1 ~v2 ~v3 = du_k'45'dropl_1020
du_k'45'dropl_1020 :: MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'dropl_1020
  = coe
      MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
      (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1200)
      (coe
         MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1182
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1246)
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1152))
-- Once.LinCore.PassTr.withE
d_withE_1030 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_withE_1030 ~v0 v1 v2 ~v3 v4 = du_withE_1030 v1 v2 v4
du_withE_1030 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_withE_1030 v0 v1 v2
  = coe
      MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
      (coe
         MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v0) (coe v1))
      (coe MAlonzo.Code.Once.LinCore.Core.C_blift_984 v2)
      (coe
         MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
         (coe
            MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
            (coe MAlonzo.Code.Once.LinCore.Core.C_One_180) (coe v1))
         (coe
            MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808
            (coe
               MAlonzo.Code.Once.LinCore.Core.C_bsnd_1004
               (coe MAlonzo.Code.Once.LinCore.Core.C_bcopy_1026))
            (coe MAlonzo.Code.Once.LinCore.Core.C_lid_786))
         (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_832))
-- Once.LinCore.PassTr.k-withE
d_k'45'withE_1044 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'withE_1044 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_k'45'withE_1044 v5
du_k'45'withE_1044 ::
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'withE_1044 v0
  = coe
      MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
      (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lift_1370 v0)
      (coe
         MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
         (coe
            MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1182
            (coe
               MAlonzo.Code.Once.LinCore.Core.C_k'45'snd_1394
               (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'copy_1422))
            (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1152))
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1206))
-- Once.LinCore.PassTr.copyIn
d_copyIn_1056 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_copyIn_1056 ~v0 v1 v2 ~v3 v4 = du_copyIn_1056 v1 v2 v4
du_copyIn_1056 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_copyIn_1056 v0 v1 v2
  = coe
      MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
      (coe
         MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v0) (coe v1))
      (coe MAlonzo.Code.Once.LinCore.Core.C_blift_984 v2)
      (coe
         MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
         (coe
            MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
            (coe MAlonzo.Code.Once.LinCore.Core.C_One_180) (coe v1))
         (coe
            MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808
            (coe MAlonzo.Code.Once.LinCore.Core.C_bcopy_1026)
            (coe MAlonzo.Code.Once.LinCore.Core.C_lid_786))
         (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_832))
-- Once.LinCore.PassTr.k-copyIn
d_k'45'copyIn_1070 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'copyIn_1070 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_k'45'copyIn_1070 v5
du_k'45'copyIn_1070 ::
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'copyIn_1070 v0
  = coe
      MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
      (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lift_1370 v0)
      (coe
         MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
         (coe
            MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1182
            (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'copy_1422)
            (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1152))
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1206))
-- Once.LinCore.PassTr.mapL
d_mapL_1084 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_mapL_1084 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_mapL_1084 v4 v5 v6
du_mapL_1084 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_mapL_1084 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.LinCore.Core.C_Idf_136 -> coe v2
      MAlonzo.Code.Once.LinCore.Core.C_Kone_138
        -> coe MAlonzo.Code.Once.LinCore.Core.C_lid_786
      MAlonzo.Code.Once.LinCore.Core.C_Kzero_140
        -> coe MAlonzo.Code.Once.LinCore.Core.C_lid_786
      MAlonzo.Code.Once.LinCore.Core.C_Kb_142 v3
        -> coe MAlonzo.Code.Once.LinCore.Core.C_lid_786
      MAlonzo.Code.Once.LinCore.Core.C_Kμ_144 v3
        -> coe MAlonzo.Code.Once.LinCore.Core.C_lid_786
      MAlonzo.Code.Once.LinCore.Core.C__'8853'f__146 v3 v4
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_lcase_898
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                (coe
                   MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v3) (coe v0))
                (coe MAlonzo.Code.Once.LinCore.Core.C_linl_880)
                (coe du_mapL_1084 (coe v0) (coe v3) (coe v2)))
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                (coe
                   MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v4) (coe v0))
                (coe MAlonzo.Code.Once.LinCore.Core.C_linr_888)
                (coe du_mapL_1084 (coe v0) (coe v4) (coe v2)))
      MAlonzo.Code.Once.LinCore.Core.C__'8855'f__148 v3 v4
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808
             (coe du_mapL_1084 (coe v0) (coe v3) (coe v2))
             (coe du_mapL_1084 (coe v0) (coe v4) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.PassTr.k-mapL
d_k'45'mapL_1124 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'mapL_1124 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7
  = du_k'45'mapL_1124 v5 v7
du_k'45'mapL_1124 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'mapL_1124 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_Idf_136 -> coe v1
      MAlonzo.Code.Once.LinCore.Core.C_Kone_138
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1152
      MAlonzo.Code.Once.LinCore.Core.C_Kzero_140
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1152
      MAlonzo.Code.Once.LinCore.Core.C_Kb_142 v2
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1152
      MAlonzo.Code.Once.LinCore.Core.C_Kμ_144 v2
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1152
      MAlonzo.Code.Once.LinCore.Core.C__'8853'f__146 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45'case_1276
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inl_1254)
                (coe du_k'45'mapL_1124 (coe v2) (coe v1)))
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inr_1262)
                (coe du_k'45'mapL_1124 (coe v3) (coe v1)))
      MAlonzo.Code.Once.LinCore.Core.C__'8855'f__148 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1182
             (coe du_k'45'mapL_1124 (coe v2) (coe v1))
             (coe du_k'45'mapL_1124 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.PassTr.InS
d_InS_1152 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_InS_1152 ~v0 v1 = du_InS_1152 v1
du_InS_1152 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
du_InS_1152 v0
  = coe
      MAlonzo.Code.Once.LinCore.Core.C__'8853't__186
      (coe
         MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v0)
         (coe MAlonzo.Code.Once.LinCore.Core.C_Nu_192 (coe v0)))
      (coe MAlonzo.Code.Once.LinCore.Core.C_Nu_192 (coe v0))
-- Once.LinCore.PassTr.inco
d_inco_1160 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_inco_1160 ~v0 ~v1 v2 = du_inco_1160 v2
du_inco_1160 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_inco_1160 v0
  = coe
      MAlonzo.Code.Once.LinCore.Core.C_lcase_898
      (coe
         du_mapL_1084 (coe du_InS_1152 (coe v0)) (coe v0)
         (coe MAlonzo.Code.Once.LinCore.Core.C_linr_888))
      (coe
         MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
         (coe
            MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v0)
            (coe MAlonzo.Code.Once.LinCore.Core.C_Nu_192 (coe v0)))
         (coe
            du_mapL_1084 (coe du_InS_1152 (coe v0)) (coe v0)
            (coe MAlonzo.Code.Once.LinCore.Core.C_linr_888))
         (coe MAlonzo.Code.Once.LinCore.Core.C_lout_1122))
-- Once.LinCore.PassTr.k-inco
d_k'45'inco_1168 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'inco_1168 ~v0 ~v1 v2 = du_k'45'inco_1168 v2
du_k'45'inco_1168 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'inco_1168 v0
  = coe
      MAlonzo.Code.Once.LinCore.Core.C_k'45'case_1276
      (coe
         du_k'45'mapL_1124 (coe v0)
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inr_1262))
      (coe
         MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
         (coe
            du_k'45'mapL_1124 (coe v0)
            (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inr_1262))
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'nout_1518))
-- Once.LinCore.PassTr.tr
d_tr_1178 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_692 -> MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_tr_1178 ~v0 ~v1 v2 v3 v4 = du_tr_1178 v2 v3 v4
du_tr_1178 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_692 -> MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_tr_1178 v0 v1 v2
  = case coe v2 of
      C_id_708 -> coe MAlonzo.Code.Once.LinCore.Core.C_lid_786
      C__'8728'__716 v4 v6 v7
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v4
             (coe du_tr_1178 (coe v4) (coe v1) (coe v6))
             (coe du_tr_1178 (coe v0) (coe v4) (coe v7))
      C_'10216'_'44'_'10217'_724 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v8 v9
               -> coe
                    MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                    (coe
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v0) (coe v0))
                    (coe
                       MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808
                       (coe du_tr_1178 (coe v0) (coe v8) (coe v6))
                       (coe du_tr_1178 (coe v0) (coe v9) (coe v7)))
                    (coe MAlonzo.Code.Once.LinCore.Core.C_dup_866)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fst_730
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v1)
                (coe MAlonzo.Code.Once.LinCore.Core.C_One_180))
             (coe MAlonzo.Code.Once.LinCore.Core.C_ρl_814)
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808
                (coe MAlonzo.Code.Once.LinCore.Core.C_lid_786)
                (coe MAlonzo.Code.Once.LinCore.Core.C_drop_872))
      C_snd_736
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                (coe MAlonzo.Code.Once.LinCore.Core.C_One_180) (coe v1))
             (coe MAlonzo.Code.Once.LinCore.Core.C_lul_826)
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808
                (coe MAlonzo.Code.Once.LinCore.Core.C_drop_872)
                (coe MAlonzo.Code.Once.LinCore.Core.C_lid_786))
      C_inl_742 -> coe MAlonzo.Code.Once.LinCore.Core.C_linl_880
      C_inr_748 -> coe MAlonzo.Code.Once.LinCore.Core.C_linr_888
      C_case_756 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v8 v9
               -> coe
                    MAlonzo.Code.Once.LinCore.Core.C_lcase_898
                    (coe du_tr_1178 (coe v8) (coe v1) (coe v6))
                    (coe du_tr_1178 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_terminal_760 -> coe MAlonzo.Code.Once.LinCore.Core.C_drop_872
      C_initial_764 -> coe MAlonzo.Code.Once.LinCore.Core.C_lzero_904
      C_curry_776 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v9 v10 v11 v12
               -> coe
                    MAlonzo.Code.Once.LinCore.Core.C_llamω_1066
                    (coe
                       MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v0) (coe v11))
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C_blift_984
                          (coe
                             du_tr_1178
                             (coe
                                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v0) (coe v11))
                             (coe v12) (coe v7)))
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                             (coe MAlonzo.Code.Once.LinCore.Core.C_One_180) (coe v11))
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808
                             (coe MAlonzo.Code.Once.LinCore.Core.C_bcopy_1026)
                             (coe MAlonzo.Code.Once.LinCore.Core.C_lid_786))
                          (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_832)))
                    (coe
                       du_tr'45'gd_1202 (coe v10) (coe v0) (coe v11) (coe v12) (coe v7)
                       (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_apply_784
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v8 v9 v10 v11
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C_Fn_190
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_many_154) (coe v9) (coe v10)
                                 (coe v1))
                              (coe v1))
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180) (coe v1))
                              (coe MAlonzo.Code.Once.LinCore.Core.C_lul_826)
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_drop_872)
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_lid_786)))
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C_lend_976
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C_bsnd_1004
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_bev_1084)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_In_788 -> coe MAlonzo.Code.Once.LinCore.Core.C_lIn_920
      C_out'45'μ_792 -> coe MAlonzo.Code.Once.LinCore.Core.C_lOutμ_926
      C_Cata_800 v6
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v7 v8
               -> case coe v8 of
                    MAlonzo.Code.Once.LinCore.Core.C_μt_194 v9
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v7) (coe v1))
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180) (coe v1))
                              (coe MAlonzo.Code.Once.LinCore.Core.C_lul_826)
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_drop_872)
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_lid_786)))
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C_lend_976
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C_lcata_934
                                 (coe
                                    MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                                    (coe
                                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v7)
                                       (coe
                                          MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v9)
                                          (coe v1)))
                                    (coe
                                       MAlonzo.Code.Once.LinCore.Core.C_blift_984
                                       (coe
                                          du_tr_1178
                                          (coe
                                             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v7)
                                             (coe
                                                MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198
                                                (coe v9) (coe v1)))
                                          (coe v1) (coe v6)))
                                    (coe
                                       MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                                       (coe
                                          MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                                          (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                                          (coe
                                             MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v9)
                                             (coe v1)))
                                       (coe
                                          MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808
                                          (coe
                                             MAlonzo.Code.Once.LinCore.Core.C_bsnd_1004
                                             (coe MAlonzo.Code.Once.LinCore.Core.C_bcopy_1026))
                                          (coe MAlonzo.Code.Once.LinCore.Core.C_lid_786))
                                       (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_832)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Ana_810 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v8 v9
               -> case coe v1 of
                    MAlonzo.Code.Once.LinCore.Core.C_Nu_192 v10
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C_Fn_190
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_many_154)
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_act_158) (coe v9)
                                 (coe
                                    MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v10)
                                    (coe v9)))
                              (coe v9))
                           (coe MAlonzo.Code.Once.LinCore.Core.C_lunf_1116)
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C_llamω_1066
                                 (coe
                                    MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v0
                                    (coe
                                       MAlonzo.Code.Once.LinCore.Core.C_blift_984
                                       (coe
                                          du_tr_1178 (coe v0)
                                          (coe
                                             MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198
                                             (coe v10) (coe v9))
                                          (coe v6)))
                                    (coe
                                       MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                                       (coe
                                          MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                                          (coe MAlonzo.Code.Once.LinCore.Core.C_One_180) (coe v9))
                                       (coe
                                          MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808
                                          (coe MAlonzo.Code.Once.LinCore.Core.C_bcopy_1026)
                                          (coe MAlonzo.Code.Once.LinCore.Core.C_lid_786))
                                       (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_832)))
                                 (coe
                                    MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
                                    (coe
                                       MAlonzo.Code.Once.LinCore.Core.C_k'45'lift_1370
                                       (coe
                                          du_tr'45'blk_1188 (coe v0)
                                          (coe
                                             MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198
                                             (coe v10) (coe v9))
                                          (coe v6) (coe v7)))
                                    (coe
                                       MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
                                       (coe
                                          MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1182
                                          (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'copy_1422)
                                          (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1152))
                                       (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1206))))
                              (coe MAlonzo.Code.Once.LinCore.Core.C_lid_786))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Out_814 -> coe MAlonzo.Code.Once.LinCore.Core.C_lout_1122
      C_in'45'ν_818
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C_Nu_192 v4
               -> coe
                    MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                    (coe
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C_Fn_190
                          (coe MAlonzo.Code.Once.LinCore.Core.C_many_154)
                          (coe MAlonzo.Code.Once.LinCore.Core.C_act_158)
                          (coe du_InS_1152 (coe v4))
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v4)
                             (coe du_InS_1152 (coe v4))))
                       (coe du_InS_1152 (coe v4)))
                    (coe MAlonzo.Code.Once.LinCore.Core.C_lunf_1116)
                    (coe
                       MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                          (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v4) (coe v1)))
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.C_llamω_1066
                             (coe du_inco_1160 (coe v4)) (coe du_k'45'inco_1168 (coe v4)))
                          (coe MAlonzo.Code.Once.LinCore.Core.C_linl_880))
                       (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_832))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Iter_828 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v8 v9
               -> coe
                    MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                    (coe
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v8) (coe v1))
                    (coe
                       MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                          (coe MAlonzo.Code.Once.LinCore.Core.C_One_180) (coe v1))
                       (coe MAlonzo.Code.Once.LinCore.Core.C_lul_826)
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808
                          (coe MAlonzo.Code.Once.LinCore.Core.C_drop_872)
                          (coe MAlonzo.Code.Once.LinCore.Core.C_lid_786)))
                    (coe
                       MAlonzo.Code.Once.LinCore.Core.C_lend_976
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C_liter_1144
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v0
                             (coe
                                MAlonzo.Code.Once.LinCore.Core.C_blift_984
                                (coe
                                   du_tr_1178 (coe v0)
                                   (coe
                                      MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 (coe v1)
                                      (coe v9))
                                   (coe v6)))
                             (coe
                                MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                                (coe
                                   MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                                   (coe MAlonzo.Code.Once.LinCore.Core.C_One_180) (coe v9))
                                (coe
                                   MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808
                                   (coe
                                      MAlonzo.Code.Once.LinCore.Core.C_bsnd_1004
                                      (coe MAlonzo.Code.Once.LinCore.Core.C_bcopy_1026))
                                   (coe MAlonzo.Code.Once.LinCore.Core.C_lid_786))
                                (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_832)))
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
                             (coe
                                MAlonzo.Code.Once.LinCore.Core.C_k'45'lift_1370
                                (coe
                                   du_tr'45'blk_1188 (coe v0)
                                   (coe
                                      MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 (coe v1)
                                      (coe v9))
                                   (coe v6) (coe v7)))
                             (coe
                                MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
                                (coe
                                   MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1182
                                   (coe
                                      MAlonzo.Code.Once.LinCore.Core.C_k'45'snd_1394
                                      (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'copy_1422))
                                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1152))
                                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1206)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_const_832 v4
        -> coe MAlonzo.Code.Once.LinCore.Core.C_lconst_1128 v4
      C_SigOp_836 v3 -> coe MAlonzo.Code.Once.LinCore.Core.C_lop_1134 v3
      C_Call_846 v3 v4 v7
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_Ct_188 (coe v3)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_One_180))
                (coe v0))
             (coe MAlonzo.Code.Once.LinCore.Core.C_lapp_966 v4 v7)
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                   (coe
                      MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198
                      (coe MAlonzo.Code.Once.LinCore.Core.C_Idf_136)
                      (coe MAlonzo.Code.Once.LinCore.Core.C_One_180))
                   (coe v0))
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808
                   (coe
                      MAlonzo.Code.Once.LinCore.Core.C_lclo_952
                      (coe MAlonzo.Code.Once.LinCore.Core.C_Idf_136) v3
                      (coe MAlonzo.Code.Once.LinCore.Core.C_once_152) v4
                      (coe MAlonzo.Code.Once.LinCore.Core.C_One_180) v0 v1 v7)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_lid_786))
                (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_832))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.PassTr.tr-blk
d_tr'45'blk_1188 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_692 -> T_BlkIR_698 -> MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_tr'45'blk_1188 ~v0 ~v1 v2 v3 v4 v5
  = du_tr'45'blk_1188 v2 v3 v4 v5
du_tr'45'blk_1188 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_692 -> T_BlkIR_698 -> MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_tr'45'blk_1188 v0 v1 v2 v3
  = case coe v3 of
      C_i'45'id_850 -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1152
      C_i'45''8728'_862 v9 v10
        -> case coe v2 of
             C__'8728'__716 v12 v14 v15
               -> coe
                    MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
                    (coe du_tr'45'blk_1188 (coe v12) (coe v1) (coe v14) (coe v9))
                    (coe du_tr'45'blk_1188 (coe v0) (coe v12) (coe v15) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_i'45'pair_874 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v11 v12
               -> case coe v2 of
                    C_'10216'_'44'_'10217'_724 v16 v17
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1182
                              (coe du_tr'45'blk_1188 (coe v0) (coe v11) (coe v16) (coe v9))
                              (coe du_tr'45'blk_1188 (coe v0) (coe v12) (coe v17) (coe v10)))
                           (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'dup_1240)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_i'45'fst_880
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'ρ_1188)
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1182
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1152)
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1246))
      C_i'45'snd_886
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1200)
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1182
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1246)
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1152))
      C_i'45'inl_892
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inl_1254
      C_i'45'inr_898
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inr_1262
      C_i'45'case_910 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v11 v12
               -> case coe v2 of
                    C_case_756 v16 v17
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C_k'45'case_1276
                           (coe du_tr'45'blk_1188 (coe v11) (coe v1) (coe v16) (coe v9))
                           (coe du_tr'45'blk_1188 (coe v12) (coe v1) (coe v17) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_i'45'term_914
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1246
      C_i'45'init_918
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'zero_1282
      C_i'45'curry_932
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lamω_1466
      C_i'45'apply_938
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1200)
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1182
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1246)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1152)))
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45'lend_1360
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_k'45'snd_1394
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'bev_1480)))
      C_i'45'In_942 -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'in_1298
      C_i'45'out_946
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'out_1304
      C_i'45'cata_956 v8
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v9 v10
               -> case coe v10 of
                    MAlonzo.Code.Once.LinCore.Core.C_μt_194 v11
                      -> case coe v2 of
                           C_Cata_800 v15
                             -> coe
                                  MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
                                  (coe
                                     MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
                                     (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1200)
                                     (coe
                                        MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1182
                                        (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1246)
                                        (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1152)))
                                  (coe
                                     MAlonzo.Code.Once.LinCore.Core.C_k'45'lend_1360
                                     (coe
                                        MAlonzo.Code.Once.LinCore.Core.C_k'45'cata_1314
                                        (coe
                                           MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
                                           (coe
                                              MAlonzo.Code.Once.LinCore.Core.C_k'45'lift_1370
                                              (coe
                                                 du_tr'45'blk_1188
                                                 (coe
                                                    MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                                                    (coe v9)
                                                    (coe
                                                       MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198
                                                       (coe v11) (coe v1)))
                                                 (coe v1) (coe v15) (coe v8)))
                                           (coe
                                              MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
                                              (coe
                                                 MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1182
                                                 (coe
                                                    MAlonzo.Code.Once.LinCore.Core.C_k'45'snd_1394
                                                    (coe
                                                       MAlonzo.Code.Once.LinCore.Core.C_k'45'copy_1422))
                                                 (coe
                                                    MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1152))
                                              (coe
                                                 MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1206)))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_i'45'ana_968
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'unf_1512)
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1182
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lamω_1466)
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1152))
      C_i'45'Out_972
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'nout_1518
      C_i'45'inν_976
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'unf_1512)
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1182
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lamω_1466)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inl_1254))
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1206))
      C_i'45'const_982
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'const_1526
      C_i'45'op_986 -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'op_1532
      C_i'45'call_996
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'app_1348)
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1182
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'clo_1334)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1152))
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1206))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.PassTr.tr-gd
d_tr'45'gd_1202 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_692 -> AgdaAny -> AgdaAny
d_tr'45'gd_1202 ~v0 v1 ~v2 v3 v4 v5 v6 v7
  = du_tr'45'gd_1202 v1 v3 v4 v5 v6 v7
du_tr'45'gd_1202 ::
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_692 -> AgdaAny -> AgdaAny
du_tr'45'gd_1202 v0 v1 v2 v3 v4 v5
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_act_158
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45'lift_1370
                (coe
                   du_tr'45'blk_1188
                   (coe
                      MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v1) (coe v2))
                   (coe v3) (coe v4) (coe v5)))
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1182
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'copy_1422)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1152))
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1206))
      MAlonzo.Code.Once.LinCore.Core.C_eff_160
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.PassTr.Prog
d_Prog_1266 a0 a1 = ()
data T_Prog_1266
  = C_ε_1268 | C__'9657'_'8739'__1280 T_Prog_1266 T_IR_692 AgdaAny
-- Once.LinCore.PassTr.tr-def
d_tr'45'def_1292 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_692 -> AgdaAny -> AgdaAny
d_tr'45'def_1292 ~v0 v1 ~v2 v3 v4 v5 v6
  = du_tr'45'def_1292 v1 v3 v4 v5 v6
du_tr'45'def_1292 ::
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_692 -> AgdaAny -> AgdaAny
du_tr'45'def_1292 v0 v1 v2 v3 v4
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_act_158
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
             (coe du_tr'45'blk_1188 (coe v1) (coe v2) (coe v3) (coe v4))
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1200)
      MAlonzo.Code.Once.LinCore.Core.C_eff_160
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.PassTr.trP
d_trP_1298 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  T_Prog_1266 -> MAlonzo.Code.Once.LinCore.Core.T_Defs_2078
d_trP_1298 ~v0 v1 v2 = du_trP_1298 v1 v2
du_trP_1298 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  T_Prog_1266 -> MAlonzo.Code.Once.LinCore.Core.T_Defs_2078
du_trP_1298 v0 v1
  = case coe v1 of
      C_ε_1268 -> coe MAlonzo.Code.Once.LinCore.Core.C_ε_2080
      C__'9657'_'8739'__1280 v6 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'9656'__732 v9 v10
               -> case coe v10 of
                    MAlonzo.Code.Once.LinCore.Core.C_sg_726 v11 v12 v13 v14 v15
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C__'9656'__2086
                           (coe du_trP_1298 (coe v9) (coe v6))
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C_b1_2064
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v14
                                 (coe du_tr_1178 (coe v14) (coe v15) (coe v7))
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_lul_826))
                              (coe
                                 du_tr'45'def_1292 (coe v12) (coe v14) (coe v15) (coe v7) (coe v8)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
