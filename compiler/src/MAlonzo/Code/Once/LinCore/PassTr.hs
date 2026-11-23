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
d_scod_324 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
d_scod_324 ~v0 = du_scod_324
du_scod_324 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
du_scod_324 = coe MAlonzo.Code.Once.LinCore.Core.du_scod_698
-- Once.LinCore.PassTr._.sdom
d_sdom_326 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
d_sdom_326 ~v0 = du_sdom_326
du_sdom_326 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
du_sdom_326 = coe MAlonzo.Code.Once.LinCore.Core.du_sdom_696
-- Once.LinCore.PassTr._.⌜_⌝
d_'8988'_'8989'_356 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_'8988'_'8989'_356 ~v0 = du_'8988'_'8989'_356
du_'8988'_'8989'_356 ::
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
du_'8988'_'8989'_356
  = coe MAlonzo.Code.Once.LinCore.Core.du_'8988'_'8989'_532
-- Once.LinCore.PassTr._.Sg.cod
d_cod_536 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_cod_536 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_cod_724 (coe v0)
-- Once.LinCore.PassTr._.Sg.dom
d_dom_538 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_dom_538 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_dom_722 (coe v0)
-- Once.LinCore.PassTr._.Sg.env
d_env_540 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_env_540 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_env_720 (coe v0)
-- Once.LinCore.PassTr._.Sg.gr
d_gr_542 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156
d_gr_542 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_gr_718 (coe v0)
-- Once.LinCore.PassTr._.Sg.kd
d_kd_544 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Kd_150
d_kd_544 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_kd_716 (coe v0)
-- Once.LinCore.PassTr._.Sig.info
d_info_548 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_info_548 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_info_692 (coe v0)
-- Once.LinCore.PassTr._.Sig.sA
d_sA_550 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_sA_550 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_sA_688 (coe v0)
-- Once.LinCore.PassTr._.Sig.sB
d_sB_552 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_sB_552 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_sB_690 (coe v0)
-- Once.LinCore.PassTr._.IR
d_IR_642 a0 a1 a2 a3 = ()
data T_IR_642
  = C_id_658 |
    C__'8728'__666 MAlonzo.Code.Once.LinCore.Core.T_LTy_178 T_IR_642
                   T_IR_642 |
    C_'10216'_'44'_'10217'_674 T_IR_642 T_IR_642 | C_fst_680 |
    C_snd_686 | C_inl_692 | C_inr_698 | C_case_706 T_IR_642 T_IR_642 |
    C_terminal_710 | C_initial_714 | C_curry_726 T_IR_642 AgdaAny |
    C_apply_734 | C_In_738 | C_out'45'μ_742 | C_Cata_750 T_IR_642 |
    C_Ana_760 T_IR_642 T_BlkIR_648 | C_Out_764 | C_in'45'ν_768 |
    C_Iter_778 T_IR_642 T_BlkIR_648 | C_const_782 AgdaAny |
    C_SigOp_786 MAlonzo.Code.Once.LinCore.Core.T_Sig_680 |
    C_Call_796 Integer MAlonzo.Code.Once.LinCore.Core.T_Gr_156
               MAlonzo.Code.Once.LinCore.Core.T__'8715''91'_'93'__738
-- Once.LinCore.PassTr._.BlkIR
d_BlkIR_648 a0 a1 a2 a3 a4 = ()
data T_BlkIR_648
  = C_i'45'id_800 | C_i'45''8728'_812 T_BlkIR_648 T_BlkIR_648 |
    C_i'45'pair_824 T_BlkIR_648 T_BlkIR_648 | C_i'45'fst_830 |
    C_i'45'snd_836 | C_i'45'inl_842 | C_i'45'inr_848 |
    C_i'45'case_860 T_BlkIR_648 T_BlkIR_648 | C_i'45'term_864 |
    C_i'45'init_868 | C_i'45'curry_882 | C_i'45'apply_888 |
    C_i'45'In_892 | C_i'45'out_896 | C_i'45'cata_906 T_BlkIR_648 |
    C_i'45'ana_918 | C_i'45'Out_922 | C_i'45'inν_926 |
    C_i'45'const_932 | C_i'45'op_936 | C_i'45'call_946
-- Once.LinCore.PassTr._.GdIR
d_GdIR_654 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 -> T_IR_642 -> ()
d_GdIR_654 = erased
-- Once.LinCore.PassTr.dropl
d_dropl_960 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_dropl_960 ~v0 ~v1 ~v2 v3 = du_dropl_960 v3
du_dropl_960 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_dropl_960 v0
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
d_k'45'dropl_970 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'dropl_970 ~v0 ~v1 ~v2 ~v3 = du_k'45'dropl_970
du_k'45'dropl_970 :: MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'dropl_970
  = coe
      MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1156
      (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1190)
      (coe
         MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1172
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1236)
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1142))
-- Once.LinCore.PassTr.withE
d_withE_980 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_withE_980 ~v0 v1 v2 ~v3 v4 = du_withE_980 v1 v2 v4
du_withE_980 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_withE_980 v0 v1 v2
  = coe
      MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
      (coe
         MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v0) (coe v1))
      (coe MAlonzo.Code.Once.LinCore.Core.C_blift_974 v2)
      (coe
         MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
         (coe
            MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
            (coe MAlonzo.Code.Once.LinCore.Core.C_One_180) (coe v1))
         (coe
            MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808
            (coe
               MAlonzo.Code.Once.LinCore.Core.C_bsnd_994
               (coe MAlonzo.Code.Once.LinCore.Core.C_bcopy_1016))
            (coe MAlonzo.Code.Once.LinCore.Core.C_lid_786))
         (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_832))
-- Once.LinCore.PassTr.k-withE
d_k'45'withE_994 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'withE_994 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_k'45'withE_994 v5
du_k'45'withE_994 ::
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'withE_994 v0
  = coe
      MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1156
      (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lift_1350 v0)
      (coe
         MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1156
         (coe
            MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1172
            (coe
               MAlonzo.Code.Once.LinCore.Core.C_k'45'snd_1374
               (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'copy_1402))
            (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1142))
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1196))
-- Once.LinCore.PassTr.copyIn
d_copyIn_1006 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_copyIn_1006 ~v0 v1 v2 ~v3 v4 = du_copyIn_1006 v1 v2 v4
du_copyIn_1006 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_copyIn_1006 v0 v1 v2
  = coe
      MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
      (coe
         MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v0) (coe v1))
      (coe MAlonzo.Code.Once.LinCore.Core.C_blift_974 v2)
      (coe
         MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
         (coe
            MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
            (coe MAlonzo.Code.Once.LinCore.Core.C_One_180) (coe v1))
         (coe
            MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808
            (coe MAlonzo.Code.Once.LinCore.Core.C_bcopy_1016)
            (coe MAlonzo.Code.Once.LinCore.Core.C_lid_786))
         (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_832))
-- Once.LinCore.PassTr.k-copyIn
d_k'45'copyIn_1020 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'copyIn_1020 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_k'45'copyIn_1020 v5
du_k'45'copyIn_1020 ::
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'copyIn_1020 v0
  = coe
      MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1156
      (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lift_1350 v0)
      (coe
         MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1156
         (coe
            MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1172
            (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'copy_1402)
            (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1142))
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1196))
-- Once.LinCore.PassTr.mapL
d_mapL_1034 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_mapL_1034 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_mapL_1034 v4 v5 v6
du_mapL_1034 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_mapL_1034 v0 v1 v2
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
                (coe du_mapL_1034 (coe v0) (coe v3) (coe v2)))
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                (coe
                   MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v4) (coe v0))
                (coe MAlonzo.Code.Once.LinCore.Core.C_linr_888)
                (coe du_mapL_1034 (coe v0) (coe v4) (coe v2)))
      MAlonzo.Code.Once.LinCore.Core.C__'8855'f__148 v3 v4
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808
             (coe du_mapL_1034 (coe v0) (coe v3) (coe v2))
             (coe du_mapL_1034 (coe v0) (coe v4) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.PassTr.k-mapL
d_k'45'mapL_1074 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'mapL_1074 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7
  = du_k'45'mapL_1074 v5 v7
du_k'45'mapL_1074 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'mapL_1074 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_Idf_136 -> coe v1
      MAlonzo.Code.Once.LinCore.Core.C_Kone_138
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1142
      MAlonzo.Code.Once.LinCore.Core.C_Kzero_140
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1142
      MAlonzo.Code.Once.LinCore.Core.C_Kb_142 v2
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1142
      MAlonzo.Code.Once.LinCore.Core.C_Kμ_144 v2
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1142
      MAlonzo.Code.Once.LinCore.Core.C__'8853'f__146 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45'case_1266
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1156
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inl_1244)
                (coe du_k'45'mapL_1074 (coe v2) (coe v1)))
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1156
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inr_1252)
                (coe du_k'45'mapL_1074 (coe v3) (coe v1)))
      MAlonzo.Code.Once.LinCore.Core.C__'8855'f__148 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1172
             (coe du_k'45'mapL_1074 (coe v2) (coe v1))
             (coe du_k'45'mapL_1074 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.PassTr.InS
d_InS_1102 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_InS_1102 ~v0 v1 = du_InS_1102 v1
du_InS_1102 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
du_InS_1102 v0
  = coe
      MAlonzo.Code.Once.LinCore.Core.C__'8853't__186
      (coe
         MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v0)
         (coe MAlonzo.Code.Once.LinCore.Core.C_Nu_192 (coe v0)))
      (coe MAlonzo.Code.Once.LinCore.Core.C_Nu_192 (coe v0))
-- Once.LinCore.PassTr.inco
d_inco_1110 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_inco_1110 ~v0 ~v1 v2 = du_inco_1110 v2
du_inco_1110 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_inco_1110 v0
  = coe
      MAlonzo.Code.Once.LinCore.Core.C_lcase_898
      (coe
         du_mapL_1034 (coe du_InS_1102 (coe v0)) (coe v0)
         (coe MAlonzo.Code.Once.LinCore.Core.C_linr_888))
      (coe
         MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
         (coe
            MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v0)
            (coe MAlonzo.Code.Once.LinCore.Core.C_Nu_192 (coe v0)))
         (coe
            du_mapL_1034 (coe du_InS_1102 (coe v0)) (coe v0)
            (coe MAlonzo.Code.Once.LinCore.Core.C_linr_888))
         (coe MAlonzo.Code.Once.LinCore.Core.C_lout_1112))
-- Once.LinCore.PassTr.k-inco
d_k'45'inco_1118 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'inco_1118 ~v0 ~v1 v2 = du_k'45'inco_1118 v2
du_k'45'inco_1118 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'inco_1118 v0
  = coe
      MAlonzo.Code.Once.LinCore.Core.C_k'45'case_1266
      (coe
         du_k'45'mapL_1074 (coe v0)
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inr_1252))
      (coe
         MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1156
         (coe
            du_k'45'mapL_1074 (coe v0)
            (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inr_1252))
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'nout_1498))
-- Once.LinCore.PassTr.tr
d_tr_1128 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_642 -> MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_tr_1128 ~v0 ~v1 v2 v3 v4 = du_tr_1128 v2 v3 v4
du_tr_1128 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_642 -> MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_tr_1128 v0 v1 v2
  = case coe v2 of
      C_id_658 -> coe MAlonzo.Code.Once.LinCore.Core.C_lid_786
      C__'8728'__666 v4 v6 v7
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v4
             (coe du_tr_1128 (coe v4) (coe v1) (coe v6))
             (coe du_tr_1128 (coe v0) (coe v4) (coe v7))
      C_'10216'_'44'_'10217'_674 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v8 v9
               -> coe
                    MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                    (coe
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v0) (coe v0))
                    (coe
                       MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808
                       (coe du_tr_1128 (coe v0) (coe v8) (coe v6))
                       (coe du_tr_1128 (coe v0) (coe v9) (coe v7)))
                    (coe MAlonzo.Code.Once.LinCore.Core.C_dup_866)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fst_680
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
      C_snd_686
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
      C_inl_692 -> coe MAlonzo.Code.Once.LinCore.Core.C_linl_880
      C_inr_698 -> coe MAlonzo.Code.Once.LinCore.Core.C_linr_888
      C_case_706 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v8 v9
               -> coe
                    MAlonzo.Code.Once.LinCore.Core.C_lcase_898
                    (coe du_tr_1128 (coe v8) (coe v1) (coe v6))
                    (coe du_tr_1128 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_terminal_710 -> coe MAlonzo.Code.Once.LinCore.Core.C_drop_872
      C_initial_714 -> coe MAlonzo.Code.Once.LinCore.Core.C_lzero_904
      C_curry_726 v7 v8
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v9 v10 v11 v12
               -> coe
                    MAlonzo.Code.Once.LinCore.Core.C_llamω_1056
                    (coe
                       MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v0) (coe v11))
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C_blift_974
                          (coe
                             du_tr_1128
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
                             (coe MAlonzo.Code.Once.LinCore.Core.C_bcopy_1016)
                             (coe MAlonzo.Code.Once.LinCore.Core.C_lid_786))
                          (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_832)))
                    (coe
                       du_tr'45'gd_1152 (coe v10) (coe v0) (coe v11) (coe v12) (coe v7)
                       (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_apply_734
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
                              MAlonzo.Code.Once.LinCore.Core.C_lend_966
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C_bsnd_994
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_bev_1074)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_In_738 -> coe MAlonzo.Code.Once.LinCore.Core.C_lIn_910
      C_out'45'μ_742 -> coe MAlonzo.Code.Once.LinCore.Core.C_lOutμ_916
      C_Cata_750 v6
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
                              MAlonzo.Code.Once.LinCore.Core.C_lend_966
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C_lcata_924
                                 (coe
                                    MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                                    (coe
                                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v7)
                                       (coe
                                          MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v9)
                                          (coe v1)))
                                    (coe
                                       MAlonzo.Code.Once.LinCore.Core.C_blift_974
                                       (coe
                                          du_tr_1128
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
                                             MAlonzo.Code.Once.LinCore.Core.C_bsnd_994
                                             (coe MAlonzo.Code.Once.LinCore.Core.C_bcopy_1016))
                                          (coe MAlonzo.Code.Once.LinCore.Core.C_lid_786))
                                       (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_832)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Ana_760 v6 v7
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
                           (coe MAlonzo.Code.Once.LinCore.Core.C_lunf_1106)
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C_llamω_1056
                                 (coe
                                    MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v0
                                    (coe
                                       MAlonzo.Code.Once.LinCore.Core.C_blift_974
                                       (coe
                                          du_tr_1128 (coe v0)
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
                                          (coe MAlonzo.Code.Once.LinCore.Core.C_bcopy_1016)
                                          (coe MAlonzo.Code.Once.LinCore.Core.C_lid_786))
                                       (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_832)))
                                 (coe
                                    MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1156
                                    (coe
                                       MAlonzo.Code.Once.LinCore.Core.C_k'45'lift_1350
                                       (coe
                                          du_tr'45'blk_1138 (coe v0)
                                          (coe
                                             MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198
                                             (coe v10) (coe v9))
                                          (coe v6) (coe v7)))
                                    (coe
                                       MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1156
                                       (coe
                                          MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1172
                                          (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'copy_1402)
                                          (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1142))
                                       (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1196))))
                              (coe MAlonzo.Code.Once.LinCore.Core.C_lid_786))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Out_764 -> coe MAlonzo.Code.Once.LinCore.Core.C_lout_1112
      C_in'45'ν_768
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
                          (coe du_InS_1102 (coe v4))
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v4)
                             (coe du_InS_1102 (coe v4))))
                       (coe du_InS_1102 (coe v4)))
                    (coe MAlonzo.Code.Once.LinCore.Core.C_lunf_1106)
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
                             MAlonzo.Code.Once.LinCore.Core.C_llamω_1056
                             (coe du_inco_1110 (coe v4)) (coe du_k'45'inco_1118 (coe v4)))
                          (coe MAlonzo.Code.Once.LinCore.Core.C_linl_880))
                       (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_832))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Iter_778 v6 v7
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
                       MAlonzo.Code.Once.LinCore.Core.C_lend_966
                       (coe
                          MAlonzo.Code.Once.LinCore.Core.C_liter_1134
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v0
                             (coe
                                MAlonzo.Code.Once.LinCore.Core.C_blift_974
                                (coe
                                   du_tr_1128 (coe v0)
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
                                      MAlonzo.Code.Once.LinCore.Core.C_bsnd_994
                                      (coe MAlonzo.Code.Once.LinCore.Core.C_bcopy_1016))
                                   (coe MAlonzo.Code.Once.LinCore.Core.C_lid_786))
                                (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_832)))
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1156
                             (coe
                                MAlonzo.Code.Once.LinCore.Core.C_k'45'lift_1350
                                (coe
                                   du_tr'45'blk_1138 (coe v0)
                                   (coe
                                      MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 (coe v1)
                                      (coe v9))
                                   (coe v6) (coe v7)))
                             (coe
                                MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1156
                                (coe
                                   MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1172
                                   (coe
                                      MAlonzo.Code.Once.LinCore.Core.C_k'45'snd_1374
                                      (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'copy_1402))
                                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1142))
                                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1196)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_const_782 v4
        -> coe MAlonzo.Code.Once.LinCore.Core.C_lconst_1118 v4
      C_SigOp_786 v3 -> coe MAlonzo.Code.Once.LinCore.Core.C_lop_1124 v3
      C_Call_796 v3 v4 v7
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_Ct_188 (coe v3)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_One_180))
                (coe v0))
             (coe MAlonzo.Code.Once.LinCore.Core.C_lapp_956 v4 v7)
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
                      MAlonzo.Code.Once.LinCore.Core.C_lclo_942
                      (coe MAlonzo.Code.Once.LinCore.Core.C_Idf_136) v3
                      (coe MAlonzo.Code.Once.LinCore.Core.C_once_152) v4
                      (coe MAlonzo.Code.Once.LinCore.Core.C_One_180) v0 v1 v7)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_lid_786))
                (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_832))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.PassTr.tr-blk
d_tr'45'blk_1138 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_642 -> T_BlkIR_648 -> MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_tr'45'blk_1138 ~v0 ~v1 v2 v3 v4 v5
  = du_tr'45'blk_1138 v2 v3 v4 v5
du_tr'45'blk_1138 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_642 -> T_BlkIR_648 -> MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_tr'45'blk_1138 v0 v1 v2 v3
  = case coe v3 of
      C_i'45'id_800 -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1142
      C_i'45''8728'_812 v9 v10
        -> case coe v2 of
             C__'8728'__666 v12 v14 v15
               -> coe
                    MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1156
                    (coe du_tr'45'blk_1138 (coe v12) (coe v1) (coe v14) (coe v9))
                    (coe du_tr'45'blk_1138 (coe v0) (coe v12) (coe v15) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_i'45'pair_824 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v11 v12
               -> case coe v2 of
                    C_'10216'_'44'_'10217'_674 v16 v17
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1156
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1172
                              (coe du_tr'45'blk_1138 (coe v0) (coe v11) (coe v16) (coe v9))
                              (coe du_tr'45'blk_1138 (coe v0) (coe v12) (coe v17) (coe v10)))
                           (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'dup_1230)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_i'45'fst_830
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1156
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'ρ_1178)
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1172
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1142)
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1236))
      C_i'45'snd_836
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1156
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1190)
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1172
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1236)
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1142))
      C_i'45'inl_842
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inl_1244
      C_i'45'inr_848
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inr_1252
      C_i'45'case_860 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v11 v12
               -> case coe v2 of
                    C_case_706 v16 v17
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C_k'45'case_1266
                           (coe du_tr'45'blk_1138 (coe v11) (coe v1) (coe v16) (coe v9))
                           (coe du_tr'45'blk_1138 (coe v12) (coe v1) (coe v17) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_i'45'term_864
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1236
      C_i'45'init_868
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'zero_1272
      C_i'45'curry_882
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lamω_1446
      C_i'45'apply_888
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1156
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1156
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1190)
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1172
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1236)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1142)))
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45'lend_1340
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_k'45'snd_1374
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'bev_1460)))
      C_i'45'In_892 -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'in_1278
      C_i'45'out_896
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'out_1284
      C_i'45'cata_906 v8
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v9 v10
               -> case coe v10 of
                    MAlonzo.Code.Once.LinCore.Core.C_μt_194 v11
                      -> case coe v2 of
                           C_Cata_750 v15
                             -> coe
                                  MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1156
                                  (coe
                                     MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1156
                                     (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1190)
                                     (coe
                                        MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1172
                                        (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1236)
                                        (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1142)))
                                  (coe
                                     MAlonzo.Code.Once.LinCore.Core.C_k'45'lend_1340
                                     (coe
                                        MAlonzo.Code.Once.LinCore.Core.C_k'45'cata_1294
                                        (coe
                                           MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1156
                                           (coe
                                              MAlonzo.Code.Once.LinCore.Core.C_k'45'lift_1350
                                              (coe
                                                 du_tr'45'blk_1138
                                                 (coe
                                                    MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                                                    (coe v9)
                                                    (coe
                                                       MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198
                                                       (coe v11) (coe v1)))
                                                 (coe v1) (coe v15) (coe v8)))
                                           (coe
                                              MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1156
                                              (coe
                                                 MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1172
                                                 (coe
                                                    MAlonzo.Code.Once.LinCore.Core.C_k'45'snd_1374
                                                    (coe
                                                       MAlonzo.Code.Once.LinCore.Core.C_k'45'copy_1402))
                                                 (coe
                                                    MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1142))
                                              (coe
                                                 MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1196)))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_i'45'ana_918
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1156
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'unf_1492)
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1172
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lamω_1446)
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1142))
      C_i'45'Out_922
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'nout_1498
      C_i'45'inν_926
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1156
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'unf_1492)
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1156
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1172
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lamω_1446)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inl_1244))
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1196))
      C_i'45'const_932
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'const_1506
      C_i'45'op_936 -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'op_1512
      C_i'45'call_946
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1156
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'app_1328)
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1156
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1172
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'clo_1314)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1142))
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1196))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.PassTr.tr-gd
d_tr'45'gd_1152 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_642 -> AgdaAny -> AgdaAny
d_tr'45'gd_1152 ~v0 v1 ~v2 v3 v4 v5 v6 v7
  = du_tr'45'gd_1152 v1 v3 v4 v5 v6 v7
du_tr'45'gd_1152 ::
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_642 -> AgdaAny -> AgdaAny
du_tr'45'gd_1152 v0 v1 v2 v3 v4 v5
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_act_158
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1156
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45'lift_1350
                (coe
                   du_tr'45'blk_1138
                   (coe
                      MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v1) (coe v2))
                   (coe v3) (coe v4) (coe v5)))
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1156
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1172
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'copy_1402)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1142))
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1196))
      MAlonzo.Code.Once.LinCore.Core.C_eff_160
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.PassTr.Prog
d_Prog_1216 a0 a1 = ()
data T_Prog_1216
  = C_ε_1218 | C__'9657'_'8739'__1230 T_Prog_1216 T_IR_642 AgdaAny
-- Once.LinCore.PassTr.tr-def
d_tr'45'def_1242 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_642 -> AgdaAny -> AgdaAny
d_tr'45'def_1242 ~v0 v1 ~v2 v3 v4 v5 v6
  = du_tr'45'def_1242 v1 v3 v4 v5 v6
du_tr'45'def_1242 ::
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_642 -> AgdaAny -> AgdaAny
du_tr'45'def_1242 v0 v1 v2 v3 v4
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_act_158
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1156
             (coe du_tr'45'blk_1138 (coe v1) (coe v2) (coe v3) (coe v4))
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1190)
      MAlonzo.Code.Once.LinCore.Core.C_eff_160
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.PassTr.trP
d_trP_1248 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  T_Prog_1216 -> MAlonzo.Code.Once.LinCore.Core.T_Defs_1812
d_trP_1248 ~v0 v1 v2 = du_trP_1248 v1 v2
du_trP_1248 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  T_Prog_1216 -> MAlonzo.Code.Once.LinCore.Core.T_Defs_1812
du_trP_1248 v0 v1
  = case coe v1 of
      C_ε_1218 -> coe MAlonzo.Code.Once.LinCore.Core.C_ε_1814
      C__'9657'_'8739'__1230 v6 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'9656'__732 v9 v10
               -> case coe v10 of
                    MAlonzo.Code.Once.LinCore.Core.C_sg_726 v11 v12 v13 v14 v15
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C__'9656'__1820
                           (coe du_trP_1248 (coe v9) (coe v6))
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C_b1_1798
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v14
                                 (coe du_tr_1128 (coe v14) (coe v15) (coe v7))
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_lul_826))
                              (coe
                                 du_tr'45'def_1242 (coe v12) (coe v14) (coe v15) (coe v7) (coe v8)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
