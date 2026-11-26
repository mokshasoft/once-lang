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
d_Sg_88 a0 = ()
-- Once.LinCore.PassTr._.Sig
d_Sig_92 a0 = ()
-- Once.LinCore.PassTr._.Tm
d_Tm_96 a0 a1 a2 a3 a4 = ()
-- Once.LinCore.PassTr._.scod
d_scod_328 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
d_scod_328 ~v0 = du_scod_328
du_scod_328 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
du_scod_328 = coe MAlonzo.Code.Once.LinCore.Core.du_scod_698
-- Once.LinCore.PassTr._.sdom
d_sdom_330 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
d_sdom_330 ~v0 = du_sdom_330
du_sdom_330 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
du_sdom_330 = coe MAlonzo.Code.Once.LinCore.Core.du_sdom_696
-- Once.LinCore.PassTr._.⌜_⌝
d_'8988'_'8989'_360 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_'8988'_'8989'_360 ~v0 = du_'8988'_'8989'_360
du_'8988'_'8989'_360 ::
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
du_'8988'_'8989'_360
  = coe MAlonzo.Code.Once.LinCore.Core.du_'8988'_'8989'_532
-- Once.LinCore.PassTr._.Sg.cod
d_cod_542 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_cod_542 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_cod_724 (coe v0)
-- Once.LinCore.PassTr._.Sg.dom
d_dom_544 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_dom_544 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_dom_722 (coe v0)
-- Once.LinCore.PassTr._.Sg.env
d_env_546 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_env_546 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_env_720 (coe v0)
-- Once.LinCore.PassTr._.Sg.gr
d_gr_548 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156
d_gr_548 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_gr_718 (coe v0)
-- Once.LinCore.PassTr._.Sg.kd
d_kd_550 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Kd_150
d_kd_550 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_kd_716 (coe v0)
-- Once.LinCore.PassTr._.Sig.info
d_info_554 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_info_554 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_info_692 (coe v0)
-- Once.LinCore.PassTr._.Sig.sA
d_sA_556 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_sA_556 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_sA_688 (coe v0)
-- Once.LinCore.PassTr._.Sig.sB
d_sB_558 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_sB_558 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_sB_690 (coe v0)
-- Once.LinCore.PassTr._.IR
d_IR_650 a0 a1 a2 a3 = ()
data T_IR_650
  = C_id_666 |
    C__'8728'__674 MAlonzo.Code.Once.LinCore.Core.T_LTy_178 T_IR_650
                   T_IR_650 |
    C_'10216'_'44'_'10217'_682 T_IR_650 T_IR_650 | C_fst_688 |
    C_snd_694 | C_inl_700 | C_inr_706 | C_case_714 T_IR_650 T_IR_650 |
    C_terminal_718 | C_initial_722 | C_curry_734 T_IR_650 AgdaAny |
    C_apply_742 | C_In_746 | C_out'45'μ_750 | C_Cata_758 T_IR_650 |
    C_Ana_768 T_IR_650 T_BlkIR_656 | C_Out_772 | C_in'45'ν_776 |
    C_Iter_786 T_IR_650 T_BlkIR_656 | C_const_790 AgdaAny |
    C_SigOp_794 MAlonzo.Code.Once.LinCore.Core.T_Sig_680 |
    C_Call_804 Integer MAlonzo.Code.Once.LinCore.Core.T_Gr_156
               MAlonzo.Code.Once.LinCore.Core.T__'8715''91'_'93'__738
-- Once.LinCore.PassTr._.BlkIR
d_BlkIR_656 a0 a1 a2 a3 a4 = ()
data T_BlkIR_656
  = C_i'45'id_808 | C_i'45''8728'_820 T_BlkIR_656 T_BlkIR_656 |
    C_i'45'pair_832 T_BlkIR_656 T_BlkIR_656 | C_i'45'fst_838 |
    C_i'45'snd_844 | C_i'45'inl_850 | C_i'45'inr_856 |
    C_i'45'case_868 T_BlkIR_656 T_BlkIR_656 | C_i'45'term_872 |
    C_i'45'init_876 | C_i'45'curry_890 | C_i'45'apply_896 |
    C_i'45'In_900 | C_i'45'out_904 | C_i'45'cata_914 T_BlkIR_656 |
    C_i'45'ana_926 | C_i'45'Out_930 | C_i'45'inν_934 |
    C_i'45'const_940 | C_i'45'op_944 | C_i'45'call_954
-- Once.LinCore.PassTr._.GdIR
d_GdIR_662 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 -> T_IR_650 -> ()
d_GdIR_662 = erased
-- Once.LinCore.PassTr.dropl
d_dropl_968 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_dropl_968 ~v0 ~v1 ~v2 v3 = du_dropl_968 v3
du_dropl_968 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_dropl_968 v0
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
d_k'45'dropl_978 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'dropl_978 ~v0 ~v1 ~v2 ~v3 = du_k'45'dropl_978
du_k'45'dropl_978 :: MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'dropl_978
  = coe
      MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
      (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1200)
      (coe
         MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1182
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1246)
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1152))
-- Once.LinCore.PassTr.withE
d_withE_988 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_withE_988 ~v0 v1 v2 ~v3 v4 = du_withE_988 v1 v2 v4
du_withE_988 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_withE_988 v0 v1 v2
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
d_k'45'withE_1002 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'withE_1002 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_k'45'withE_1002 v5
du_k'45'withE_1002 ::
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'withE_1002 v0
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
d_copyIn_1014 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_copyIn_1014 ~v0 v1 v2 ~v3 v4 = du_copyIn_1014 v1 v2 v4
du_copyIn_1014 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_copyIn_1014 v0 v1 v2
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
d_k'45'copyIn_1028 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'copyIn_1028 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_k'45'copyIn_1028 v5
du_k'45'copyIn_1028 ::
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'copyIn_1028 v0
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
d_mapL_1042 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_mapL_1042 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_mapL_1042 v4 v5 v6
du_mapL_1042 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_mapL_1042 v0 v1 v2
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
                (coe du_mapL_1042 (coe v0) (coe v3) (coe v2)))
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                (coe
                   MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v4) (coe v0))
                (coe MAlonzo.Code.Once.LinCore.Core.C_linr_888)
                (coe du_mapL_1042 (coe v0) (coe v4) (coe v2)))
      MAlonzo.Code.Once.LinCore.Core.C__'8855'f__148 v3 v4
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808
             (coe du_mapL_1042 (coe v0) (coe v3) (coe v2))
             (coe du_mapL_1042 (coe v0) (coe v4) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.PassTr.k-mapL
d_k'45'mapL_1082 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'mapL_1082 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7
  = du_k'45'mapL_1082 v5 v7
du_k'45'mapL_1082 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'mapL_1082 v0 v1
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
                (coe du_k'45'mapL_1082 (coe v2) (coe v1)))
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inr_1262)
                (coe du_k'45'mapL_1082 (coe v3) (coe v1)))
      MAlonzo.Code.Once.LinCore.Core.C__'8855'f__148 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1182
             (coe du_k'45'mapL_1082 (coe v2) (coe v1))
             (coe du_k'45'mapL_1082 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.PassTr.InS
d_InS_1110 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_InS_1110 ~v0 v1 = du_InS_1110 v1
du_InS_1110 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
du_InS_1110 v0
  = coe
      MAlonzo.Code.Once.LinCore.Core.C__'8853't__186
      (coe
         MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v0)
         (coe MAlonzo.Code.Once.LinCore.Core.C_Nu_192 (coe v0)))
      (coe MAlonzo.Code.Once.LinCore.Core.C_Nu_192 (coe v0))
-- Once.LinCore.PassTr.inco
d_inco_1118 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_inco_1118 ~v0 ~v1 v2 = du_inco_1118 v2
du_inco_1118 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_inco_1118 v0
  = coe
      MAlonzo.Code.Once.LinCore.Core.C_lcase_898
      (coe
         du_mapL_1042 (coe du_InS_1110 (coe v0)) (coe v0)
         (coe MAlonzo.Code.Once.LinCore.Core.C_linr_888))
      (coe
         MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
         (coe
            MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v0)
            (coe MAlonzo.Code.Once.LinCore.Core.C_Nu_192 (coe v0)))
         (coe
            du_mapL_1042 (coe du_InS_1110 (coe v0)) (coe v0)
            (coe MAlonzo.Code.Once.LinCore.Core.C_linr_888))
         (coe MAlonzo.Code.Once.LinCore.Core.C_lout_1122))
-- Once.LinCore.PassTr.k-inco
d_k'45'inco_1126 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'inco_1126 ~v0 ~v1 v2 = du_k'45'inco_1126 v2
du_k'45'inco_1126 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'inco_1126 v0
  = coe
      MAlonzo.Code.Once.LinCore.Core.C_k'45'case_1276
      (coe
         du_k'45'mapL_1082 (coe v0)
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inr_1262))
      (coe
         MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
         (coe
            du_k'45'mapL_1082 (coe v0)
            (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inr_1262))
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'nout_1518))
-- Once.LinCore.PassTr.tr
d_tr_1136 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_650 -> MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_tr_1136 ~v0 ~v1 v2 v3 v4 = du_tr_1136 v2 v3 v4
du_tr_1136 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_650 -> MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_tr_1136 v0 v1 v2
  = case coe v2 of
      C_id_666 -> coe MAlonzo.Code.Once.LinCore.Core.C_lid_786
      C__'8728'__674 v4 v6 v7
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v4
             (coe du_tr_1136 (coe v4) (coe v1) (coe v6))
             (coe du_tr_1136 (coe v0) (coe v4) (coe v7))
      C_'10216'_'44'_'10217'_682 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v8 v9
               -> coe
                    MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                    (coe
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v0) (coe v0))
                    (coe
                       MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808
                       (coe du_tr_1136 (coe v0) (coe v8) (coe v6))
                       (coe du_tr_1136 (coe v0) (coe v9) (coe v7)))
                    (coe MAlonzo.Code.Once.LinCore.Core.C_dup_866)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fst_688
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
      C_snd_694
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
      C_inl_700 -> coe MAlonzo.Code.Once.LinCore.Core.C_linl_880
      C_inr_706 -> coe MAlonzo.Code.Once.LinCore.Core.C_linr_888
      C_case_714 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v8 v9
               -> coe
                    MAlonzo.Code.Once.LinCore.Core.C_lcase_898
                    (coe du_tr_1136 (coe v8) (coe v1) (coe v6))
                    (coe du_tr_1136 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_terminal_718 -> coe MAlonzo.Code.Once.LinCore.Core.C_drop_872
      C_initial_722 -> coe MAlonzo.Code.Once.LinCore.Core.C_lzero_904
      C_curry_734 v7 v8
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
                             du_tr_1136
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
                       du_tr'45'gd_1160 (coe v10) (coe v0) (coe v11) (coe v12) (coe v7)
                       (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_apply_742
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
      C_In_746 -> coe MAlonzo.Code.Once.LinCore.Core.C_lIn_920
      C_out'45'μ_750 -> coe MAlonzo.Code.Once.LinCore.Core.C_lOutμ_926
      C_Cata_758 v6
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
                                          du_tr_1136
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
      C_Ana_768 v6 v7
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
                                          du_tr_1136 (coe v0)
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
                                          du_tr'45'blk_1146 (coe v0)
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
      C_Out_772 -> coe MAlonzo.Code.Once.LinCore.Core.C_lout_1122
      C_in'45'ν_776
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
                          (coe du_InS_1110 (coe v4))
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v4)
                             (coe du_InS_1110 (coe v4))))
                       (coe du_InS_1110 (coe v4)))
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
                             (coe du_inco_1118 (coe v4)) (coe du_k'45'inco_1126 (coe v4)))
                          (coe MAlonzo.Code.Once.LinCore.Core.C_linl_880))
                       (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_832))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Iter_786 v6 v7
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
                                   du_tr_1136 (coe v0)
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
                                   du_tr'45'blk_1146 (coe v0)
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
      C_const_790 v4
        -> coe MAlonzo.Code.Once.LinCore.Core.C_lconst_1128 v4
      C_SigOp_794 v3 -> coe MAlonzo.Code.Once.LinCore.Core.C_lop_1134 v3
      C_Call_804 v3 v4 v7
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
d_tr'45'blk_1146 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_650 -> T_BlkIR_656 -> MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_tr'45'blk_1146 ~v0 ~v1 v2 v3 v4 v5
  = du_tr'45'blk_1146 v2 v3 v4 v5
du_tr'45'blk_1146 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_650 -> T_BlkIR_656 -> MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_tr'45'blk_1146 v0 v1 v2 v3
  = case coe v3 of
      C_i'45'id_808 -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1152
      C_i'45''8728'_820 v9 v10
        -> case coe v2 of
             C__'8728'__674 v12 v14 v15
               -> coe
                    MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
                    (coe du_tr'45'blk_1146 (coe v12) (coe v1) (coe v14) (coe v9))
                    (coe du_tr'45'blk_1146 (coe v0) (coe v12) (coe v15) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_i'45'pair_832 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v11 v12
               -> case coe v2 of
                    C_'10216'_'44'_'10217'_682 v16 v17
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1182
                              (coe du_tr'45'blk_1146 (coe v0) (coe v11) (coe v16) (coe v9))
                              (coe du_tr'45'blk_1146 (coe v0) (coe v12) (coe v17) (coe v10)))
                           (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'dup_1240)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_i'45'fst_838
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'ρ_1188)
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1182
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1152)
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1246))
      C_i'45'snd_844
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1200)
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1182
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1246)
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1152))
      C_i'45'inl_850
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inl_1254
      C_i'45'inr_856
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inr_1262
      C_i'45'case_868 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v11 v12
               -> case coe v2 of
                    C_case_714 v16 v17
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C_k'45'case_1276
                           (coe du_tr'45'blk_1146 (coe v11) (coe v1) (coe v16) (coe v9))
                           (coe du_tr'45'blk_1146 (coe v12) (coe v1) (coe v17) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_i'45'term_872
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1246
      C_i'45'init_876
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'zero_1282
      C_i'45'curry_890
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lamω_1466
      C_i'45'apply_896
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
      C_i'45'In_900 -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'in_1298
      C_i'45'out_904
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'out_1304
      C_i'45'cata_914 v8
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v9 v10
               -> case coe v10 of
                    MAlonzo.Code.Once.LinCore.Core.C_μt_194 v11
                      -> case coe v2 of
                           C_Cata_758 v15
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
                                                 du_tr'45'blk_1146
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
      C_i'45'ana_926
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'unf_1512)
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1182
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lamω_1466)
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1152))
      C_i'45'Out_930
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'nout_1518
      C_i'45'inν_934
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
      C_i'45'const_940
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'const_1526
      C_i'45'op_944 -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'op_1532
      C_i'45'call_954
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
d_tr'45'gd_1160 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_650 -> AgdaAny -> AgdaAny
d_tr'45'gd_1160 ~v0 v1 ~v2 v3 v4 v5 v6 v7
  = du_tr'45'gd_1160 v1 v3 v4 v5 v6 v7
du_tr'45'gd_1160 ::
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_650 -> AgdaAny -> AgdaAny
du_tr'45'gd_1160 v0 v1 v2 v3 v4 v5
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_act_158
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45'lift_1370
                (coe
                   du_tr'45'blk_1146
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
d_Prog_1224 a0 a1 = ()
data T_Prog_1224
  = C_ε_1226 | C__'9657'_'8739'__1238 T_Prog_1224 T_IR_650 AgdaAny
-- Once.LinCore.PassTr.tr-def
d_tr'45'def_1250 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_650 -> AgdaAny -> AgdaAny
d_tr'45'def_1250 ~v0 v1 ~v2 v3 v4 v5 v6
  = du_tr'45'def_1250 v1 v3 v4 v5 v6
du_tr'45'def_1250 ::
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_650 -> AgdaAny -> AgdaAny
du_tr'45'def_1250 v0 v1 v2 v3 v4
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_act_158
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
             (coe du_tr'45'blk_1146 (coe v1) (coe v2) (coe v3) (coe v4))
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1200)
      MAlonzo.Code.Once.LinCore.Core.C_eff_160
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.PassTr.trP
d_trP_1256 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  T_Prog_1224 -> MAlonzo.Code.Once.LinCore.Core.T_Defs_1832
d_trP_1256 ~v0 v1 v2 = du_trP_1256 v1 v2
du_trP_1256 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  T_Prog_1224 -> MAlonzo.Code.Once.LinCore.Core.T_Defs_1832
du_trP_1256 v0 v1
  = case coe v1 of
      C_ε_1226 -> coe MAlonzo.Code.Once.LinCore.Core.C_ε_1834
      C__'9657'_'8739'__1238 v6 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'9656'__732 v9 v10
               -> case coe v10 of
                    MAlonzo.Code.Once.LinCore.Core.C_sg_726 v11 v12 v13 v14 v15
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C__'9656'__1840
                           (coe du_trP_1256 (coe v9) (coe v6))
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C_b1_1818
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v14
                                 (coe du_tr_1136 (coe v14) (coe v15) (coe v7))
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_lul_826))
                              (coe
                                 du_tr'45'def_1250 (coe v12) (coe v14) (coe v15) (coe v7) (coe v8)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
