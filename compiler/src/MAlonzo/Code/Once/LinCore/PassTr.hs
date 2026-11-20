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
d_scod_306 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
d_scod_306 ~v0 = du_scod_306
du_scod_306 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
du_scod_306 = coe MAlonzo.Code.Once.LinCore.Core.du_scod_698
-- Once.LinCore.PassTr._.sdom
d_sdom_308 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
d_sdom_308 ~v0 = du_sdom_308
du_sdom_308 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
du_sdom_308 = coe MAlonzo.Code.Once.LinCore.Core.du_sdom_696
-- Once.LinCore.PassTr._.⌜_⌝
d_'8988'_'8989'_338 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_'8988'_'8989'_338 ~v0 = du_'8988'_'8989'_338
du_'8988'_'8989'_338 ::
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
du_'8988'_'8989'_338
  = coe MAlonzo.Code.Once.LinCore.Core.du_'8988'_'8989'_532
-- Once.LinCore.PassTr._.Sg.cod
d_cod_514 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_cod_514 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_cod_724 (coe v0)
-- Once.LinCore.PassTr._.Sg.dom
d_dom_516 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_dom_516 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_dom_722 (coe v0)
-- Once.LinCore.PassTr._.Sg.env
d_env_518 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_env_518 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_env_720 (coe v0)
-- Once.LinCore.PassTr._.Sg.gr
d_gr_520 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156
d_gr_520 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_gr_718 (coe v0)
-- Once.LinCore.PassTr._.Sg.kd
d_kd_522 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Kd_150
d_kd_522 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_kd_716 (coe v0)
-- Once.LinCore.PassTr._.Sig.info
d_info_526 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_info_526 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_info_692 (coe v0)
-- Once.LinCore.PassTr._.Sig.sA
d_sA_528 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_sA_528 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_sA_688 (coe v0)
-- Once.LinCore.PassTr._.Sig.sB
d_sB_530 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_sB_530 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_sB_690 (coe v0)
-- Once.LinCore.PassTr._.IR
d_IR_616 a0 a1 a2 a3 = ()
data T_IR_616
  = C_id_632 |
    C__'8728'__640 MAlonzo.Code.Once.LinCore.Core.T_LTy_178 T_IR_616
                   T_IR_616 |
    C_'10216'_'44'_'10217'_648 T_IR_616 T_IR_616 | C_fst_654 |
    C_snd_660 | C_inl_666 | C_inr_672 | C_case_680 T_IR_616 T_IR_616 |
    C_terminal_684 | C_initial_688 | C_curry_700 T_IR_616 AgdaAny |
    C_apply_708 | C_In_712 | C_out'45'μ_716 | C_Cata_724 T_IR_616 |
    C_Ana_734 T_IR_616 T_BlkIR_622 | C_Out_738 | C_in'45'ν_742 |
    C_Iter_752 T_IR_616 T_BlkIR_622 | C_const_756 AgdaAny |
    C_SigOp_760 MAlonzo.Code.Once.LinCore.Core.T_Sig_680 |
    C_Call_770 Integer MAlonzo.Code.Once.LinCore.Core.T_Gr_156
               MAlonzo.Code.Once.LinCore.Core.T__'8715''91'_'93'__738
-- Once.LinCore.PassTr._.BlkIR
d_BlkIR_622 a0 a1 a2 a3 a4 = ()
data T_BlkIR_622
  = C_i'45'id_774 | C_i'45''8728'_786 T_BlkIR_622 T_BlkIR_622 |
    C_i'45'pair_798 T_BlkIR_622 T_BlkIR_622 | C_i'45'fst_804 |
    C_i'45'snd_810 | C_i'45'inl_816 | C_i'45'inr_822 |
    C_i'45'case_834 T_BlkIR_622 T_BlkIR_622 | C_i'45'term_838 |
    C_i'45'init_842 | C_i'45'curry_856 | C_i'45'apply_862 |
    C_i'45'In_866 | C_i'45'out_870 | C_i'45'cata_880 T_BlkIR_622 |
    C_i'45'ana_892 | C_i'45'Out_896 | C_i'45'inν_900 |
    C_i'45'const_906 | C_i'45'op_910 | C_i'45'call_920
-- Once.LinCore.PassTr._.GdIR
d_GdIR_628 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 -> T_IR_616 -> ()
d_GdIR_628 = erased
-- Once.LinCore.PassTr.dropl
d_dropl_934 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_dropl_934 ~v0 ~v1 ~v2 v3 = du_dropl_934 v3
du_dropl_934 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_dropl_934 v0
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
d_k'45'dropl_944 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'dropl_944 ~v0 ~v1 ~v2 ~v3 = du_k'45'dropl_944
du_k'45'dropl_944 :: MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'dropl_944
  = coe
      MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1132
      (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1166)
      (coe
         MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1148
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1212)
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1118))
-- Once.LinCore.PassTr.withE
d_withE_954 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_withE_954 ~v0 v1 v2 ~v3 v4 = du_withE_954 v1 v2 v4
du_withE_954 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_withE_954 v0 v1 v2
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
d_k'45'withE_968 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'withE_968 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_k'45'withE_968 v5
du_k'45'withE_968 ::
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'withE_968 v0
  = coe
      MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1132
      (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lift_1326 v0)
      (coe
         MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1132
         (coe
            MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1148
            (coe
               MAlonzo.Code.Once.LinCore.Core.C_k'45'snd_1350
               (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'copy_1378))
            (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1118))
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1172))
-- Once.LinCore.PassTr.copyIn
d_copyIn_980 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_copyIn_980 ~v0 v1 v2 ~v3 v4 = du_copyIn_980 v1 v2 v4
du_copyIn_980 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_copyIn_980 v0 v1 v2
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
d_k'45'copyIn_994 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'copyIn_994 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_k'45'copyIn_994 v5
du_k'45'copyIn_994 ::
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'copyIn_994 v0
  = coe
      MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1132
      (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lift_1326 v0)
      (coe
         MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1132
         (coe
            MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1148
            (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'copy_1378)
            (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1118))
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1172))
-- Once.LinCore.PassTr.mapL
d_mapL_1008 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_mapL_1008 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_mapL_1008 v4 v5 v6
du_mapL_1008 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_mapL_1008 v0 v1 v2
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
                (coe du_mapL_1008 (coe v0) (coe v3) (coe v2)))
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                (coe
                   MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v4) (coe v0))
                (coe MAlonzo.Code.Once.LinCore.Core.C_linr_888)
                (coe du_mapL_1008 (coe v0) (coe v4) (coe v2)))
      MAlonzo.Code.Once.LinCore.Core.C__'8855'f__148 v3 v4
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808
             (coe du_mapL_1008 (coe v0) (coe v3) (coe v2))
             (coe du_mapL_1008 (coe v0) (coe v4) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.PassTr.k-mapL
d_k'45'mapL_1048 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'mapL_1048 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7
  = du_k'45'mapL_1048 v5 v7
du_k'45'mapL_1048 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'mapL_1048 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_Idf_136 -> coe v1
      MAlonzo.Code.Once.LinCore.Core.C_Kone_138
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1118
      MAlonzo.Code.Once.LinCore.Core.C_Kzero_140
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1118
      MAlonzo.Code.Once.LinCore.Core.C_Kb_142 v2
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1118
      MAlonzo.Code.Once.LinCore.Core.C_Kμ_144 v2
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1118
      MAlonzo.Code.Once.LinCore.Core.C__'8853'f__146 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45'case_1242
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1132
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inl_1220)
                (coe du_k'45'mapL_1048 (coe v2) (coe v1)))
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1132
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inr_1228)
                (coe du_k'45'mapL_1048 (coe v3) (coe v1)))
      MAlonzo.Code.Once.LinCore.Core.C__'8855'f__148 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1148
             (coe du_k'45'mapL_1048 (coe v2) (coe v1))
             (coe du_k'45'mapL_1048 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.PassTr.InS
d_InS_1076 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_InS_1076 ~v0 v1 = du_InS_1076 v1
du_InS_1076 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
du_InS_1076 v0
  = coe
      MAlonzo.Code.Once.LinCore.Core.C__'8853't__186
      (coe
         MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v0)
         (coe MAlonzo.Code.Once.LinCore.Core.C_Nu_192 (coe v0)))
      (coe MAlonzo.Code.Once.LinCore.Core.C_Nu_192 (coe v0))
-- Once.LinCore.PassTr.inco
d_inco_1084 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_inco_1084 ~v0 ~v1 v2 = du_inco_1084 v2
du_inco_1084 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_inco_1084 v0
  = coe
      MAlonzo.Code.Once.LinCore.Core.C_lcase_898
      (coe
         du_mapL_1008 (coe du_InS_1076 (coe v0)) (coe v0)
         (coe MAlonzo.Code.Once.LinCore.Core.C_linr_888))
      (coe
         MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
         (coe
            MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v0)
            (coe MAlonzo.Code.Once.LinCore.Core.C_Nu_192 (coe v0)))
         (coe
            du_mapL_1008 (coe du_InS_1076 (coe v0)) (coe v0)
            (coe MAlonzo.Code.Once.LinCore.Core.C_linr_888))
         (coe MAlonzo.Code.Once.LinCore.Core.C_lout_1088))
-- Once.LinCore.PassTr.k-inco
d_k'45'inco_1092 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'inco_1092 ~v0 ~v1 v2 = du_k'45'inco_1092 v2
du_k'45'inco_1092 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'inco_1092 v0
  = coe
      MAlonzo.Code.Once.LinCore.Core.C_k'45'case_1242
      (coe
         du_k'45'mapL_1048 (coe v0)
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inr_1228))
      (coe
         MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1132
         (coe
            du_k'45'mapL_1048 (coe v0)
            (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inr_1228))
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'nout_1450))
-- Once.LinCore.PassTr.tr
d_tr_1102 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_616 -> MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_tr_1102 ~v0 ~v1 v2 v3 v4 = du_tr_1102 v2 v3 v4
du_tr_1102 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_616 -> MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_tr_1102 v0 v1 v2
  = case coe v2 of
      C_id_632 -> coe MAlonzo.Code.Once.LinCore.Core.C_lid_786
      C__'8728'__640 v4 v6 v7
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v4
             (coe du_tr_1102 (coe v4) (coe v1) (coe v6))
             (coe du_tr_1102 (coe v0) (coe v4) (coe v7))
      C_'10216'_'44'_'10217'_648 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v8 v9
               -> coe
                    MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                    (coe
                       MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v0) (coe v0))
                    (coe
                       MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808
                       (coe du_tr_1102 (coe v0) (coe v8) (coe v6))
                       (coe du_tr_1102 (coe v0) (coe v9) (coe v7)))
                    (coe MAlonzo.Code.Once.LinCore.Core.C_dup_866)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_fst_654
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
      C_snd_660
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
      C_inl_666 -> coe MAlonzo.Code.Once.LinCore.Core.C_linl_880
      C_inr_672 -> coe MAlonzo.Code.Once.LinCore.Core.C_linr_888
      C_case_680 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v8 v9
               -> coe
                    MAlonzo.Code.Once.LinCore.Core.C_lcase_898
                    (coe du_tr_1102 (coe v8) (coe v1) (coe v6))
                    (coe du_tr_1102 (coe v9) (coe v1) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_terminal_684 -> coe MAlonzo.Code.Once.LinCore.Core.C_drop_872
      C_initial_688 -> coe MAlonzo.Code.Once.LinCore.Core.C_lzero_904
      C_curry_700 v7 v8
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
                             du_tr_1102
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
                       du_tr'45'gd_1126 (coe v10) (coe v0) (coe v11) (coe v12) (coe v7)
                       (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_apply_708
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
      C_In_712 -> coe MAlonzo.Code.Once.LinCore.Core.C_lIn_910
      C_out'45'μ_716 -> coe MAlonzo.Code.Once.LinCore.Core.C_lOutμ_916
      C_Cata_724 v6
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
                                          du_tr_1102
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
      C_Ana_734 v6 v7
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
                           (coe MAlonzo.Code.Once.LinCore.Core.C_lunf_1082)
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C_llamω_1056
                                 (coe
                                    MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v0
                                    (coe
                                       MAlonzo.Code.Once.LinCore.Core.C_blift_974
                                       (coe
                                          du_tr_1102 (coe v0)
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
                                    MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1132
                                    (coe
                                       MAlonzo.Code.Once.LinCore.Core.C_k'45'lift_1326
                                       (coe
                                          du_tr'45'blk_1112 (coe v0)
                                          (coe
                                             MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198
                                             (coe v10) (coe v9))
                                          (coe v6) (coe v7)))
                                    (coe
                                       MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1132
                                       (coe
                                          MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1148
                                          (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'copy_1378)
                                          (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1118))
                                       (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1172))))
                              (coe MAlonzo.Code.Once.LinCore.Core.C_lid_786))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Out_738 -> coe MAlonzo.Code.Once.LinCore.Core.C_lout_1088
      C_in'45'ν_742
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
                          (coe du_InS_1076 (coe v4))
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v4)
                             (coe du_InS_1076 (coe v4))))
                       (coe du_InS_1076 (coe v4)))
                    (coe MAlonzo.Code.Once.LinCore.Core.C_lunf_1082)
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
                             (coe du_inco_1084 (coe v4)) (coe du_k'45'inco_1092 (coe v4)))
                          (coe MAlonzo.Code.Once.LinCore.Core.C_linl_880))
                       (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_832))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Iter_752 v6 v7
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
                          MAlonzo.Code.Once.LinCore.Core.C_liter_1110
                          (coe
                             MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v0
                             (coe
                                MAlonzo.Code.Once.LinCore.Core.C_blift_974
                                (coe
                                   du_tr_1102 (coe v0)
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
                             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1132
                             (coe
                                MAlonzo.Code.Once.LinCore.Core.C_k'45'lift_1326
                                (coe
                                   du_tr'45'blk_1112 (coe v0)
                                   (coe
                                      MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 (coe v1)
                                      (coe v9))
                                   (coe v6) (coe v7)))
                             (coe
                                MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1132
                                (coe
                                   MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1148
                                   (coe
                                      MAlonzo.Code.Once.LinCore.Core.C_k'45'snd_1350
                                      (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'copy_1378))
                                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1118))
                                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1172)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_const_756 v4
        -> coe MAlonzo.Code.Once.LinCore.Core.C_lconst_1094 v4
      C_SigOp_760 v3 -> coe MAlonzo.Code.Once.LinCore.Core.C_lop_1100 v3
      C_Call_770 v3 v4 v7
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
d_tr'45'blk_1112 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_616 -> T_BlkIR_622 -> MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_tr'45'blk_1112 ~v0 ~v1 v2 v3 v4 v5
  = du_tr'45'blk_1112 v2 v3 v4 v5
du_tr'45'blk_1112 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_616 -> T_BlkIR_622 -> MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_tr'45'blk_1112 v0 v1 v2 v3
  = case coe v3 of
      C_i'45'id_774 -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1118
      C_i'45''8728'_786 v9 v10
        -> case coe v2 of
             C__'8728'__640 v12 v14 v15
               -> coe
                    MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1132
                    (coe du_tr'45'blk_1112 (coe v12) (coe v1) (coe v14) (coe v9))
                    (coe du_tr'45'blk_1112 (coe v0) (coe v12) (coe v15) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_i'45'pair_798 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v11 v12
               -> case coe v2 of
                    C_'10216'_'44'_'10217'_648 v16 v17
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1132
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1148
                              (coe du_tr'45'blk_1112 (coe v0) (coe v11) (coe v16) (coe v9))
                              (coe du_tr'45'blk_1112 (coe v0) (coe v12) (coe v17) (coe v10)))
                           (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'dup_1206)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_i'45'fst_804
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1132
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'ρ_1154)
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1148
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1118)
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1212))
      C_i'45'snd_810
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1132
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1166)
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1148
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1212)
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1118))
      C_i'45'inl_816
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inl_1220
      C_i'45'inr_822
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inr_1228
      C_i'45'case_834 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v11 v12
               -> case coe v2 of
                    C_case_680 v16 v17
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C_k'45'case_1242
                           (coe du_tr'45'blk_1112 (coe v11) (coe v1) (coe v16) (coe v9))
                           (coe du_tr'45'blk_1112 (coe v12) (coe v1) (coe v17) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_i'45'term_838
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1212
      C_i'45'init_842
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'zero_1248
      C_i'45'curry_856
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lamω_1422
      C_i'45'apply_862
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1132
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1132
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1166)
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1148
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1212)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1118)))
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45'lend_1316
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_k'45'snd_1350
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'bev_1436)))
      C_i'45'In_866 -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'in_1254
      C_i'45'out_870
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'out_1260
      C_i'45'cata_880 v8
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v9 v10
               -> case coe v10 of
                    MAlonzo.Code.Once.LinCore.Core.C_μt_194 v11
                      -> case coe v2 of
                           C_Cata_724 v15
                             -> coe
                                  MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1132
                                  (coe
                                     MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1132
                                     (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1166)
                                     (coe
                                        MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1148
                                        (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1212)
                                        (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1118)))
                                  (coe
                                     MAlonzo.Code.Once.LinCore.Core.C_k'45'lend_1316
                                     (coe
                                        MAlonzo.Code.Once.LinCore.Core.C_k'45'cata_1270
                                        (coe
                                           MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1132
                                           (coe
                                              MAlonzo.Code.Once.LinCore.Core.C_k'45'lift_1326
                                              (coe
                                                 du_tr'45'blk_1112
                                                 (coe
                                                    MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                                                    (coe v9)
                                                    (coe
                                                       MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198
                                                       (coe v11) (coe v1)))
                                                 (coe v1) (coe v15) (coe v8)))
                                           (coe
                                              MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1132
                                              (coe
                                                 MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1148
                                                 (coe
                                                    MAlonzo.Code.Once.LinCore.Core.C_k'45'snd_1350
                                                    (coe
                                                       MAlonzo.Code.Once.LinCore.Core.C_k'45'copy_1378))
                                                 (coe
                                                    MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1118))
                                              (coe
                                                 MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1172)))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_i'45'ana_892
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1132
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'unf_1444)
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1148
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lamω_1422)
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1118))
      C_i'45'Out_896
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'nout_1450
      C_i'45'inν_900
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1132
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'unf_1444)
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1132
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1148
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lamω_1422)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'inl_1220))
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1172))
      C_i'45'const_906
        -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'const_1458
      C_i'45'op_910 -> coe MAlonzo.Code.Once.LinCore.Core.C_k'45'op_1464
      C_i'45'call_920
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1132
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'app_1304)
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1132
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1148
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'clo_1290)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1118))
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1172))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.PassTr.tr-gd
d_tr'45'gd_1126 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_616 -> AgdaAny -> AgdaAny
d_tr'45'gd_1126 ~v0 v1 ~v2 v3 v4 v5 v6 v7
  = du_tr'45'gd_1126 v1 v3 v4 v5 v6 v7
du_tr'45'gd_1126 ::
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_616 -> AgdaAny -> AgdaAny
du_tr'45'gd_1126 v0 v1 v2 v3 v4 v5
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_act_158
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1132
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45'lift_1326
                (coe
                   du_tr'45'blk_1112
                   (coe
                      MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v1) (coe v2))
                   (coe v3) (coe v4) (coe v5)))
             (coe
                MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1132
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1148
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'copy_1378)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1118))
                (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1172))
      MAlonzo.Code.Once.LinCore.Core.C_eff_160
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.PassTr.Prog
d_Prog_1190 a0 a1 = ()
data T_Prog_1190
  = C_ε_1192 | C__'9657'_'8739'__1204 T_Prog_1190 T_IR_616 AgdaAny
-- Once.LinCore.PassTr.tr-def
d_tr'45'def_1216 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_616 -> AgdaAny -> AgdaAny
d_tr'45'def_1216 ~v0 v1 ~v2 v3 v4 v5 v6
  = du_tr'45'def_1216 v1 v3 v4 v5 v6
du_tr'45'def_1216 ::
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_IR_616 -> AgdaAny -> AgdaAny
du_tr'45'def_1216 v0 v1 v2 v3 v4
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_act_158
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1132
             (coe du_tr'45'blk_1112 (coe v1) (coe v2) (coe v3) (coe v4))
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1166)
      MAlonzo.Code.Once.LinCore.Core.C_eff_160
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.PassTr.trP
d_trP_1222 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  T_Prog_1190 -> MAlonzo.Code.Once.LinCore.Core.T_Defs_1682
d_trP_1222 ~v0 v1 v2 = du_trP_1222 v1 v2
du_trP_1222 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  T_Prog_1190 -> MAlonzo.Code.Once.LinCore.Core.T_Defs_1682
du_trP_1222 v0 v1
  = case coe v1 of
      C_ε_1192 -> coe MAlonzo.Code.Once.LinCore.Core.C_ε_1684
      C__'9657'_'8739'__1204 v6 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'9656'__732 v9 v10
               -> case coe v10 of
                    MAlonzo.Code.Once.LinCore.Core.C_sg_726 v11 v12 v13 v14 v15
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C__'9656'__1690
                           (coe du_trP_1222 (coe v9) (coe v6))
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C_b1_1668
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796 v14
                                 (coe du_tr_1102 (coe v14) (coe v15) (coe v7))
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_lul_826))
                              (coe
                                 du_tr'45'def_1216 (coe v12) (coe v14) (coe v15) (coe v7) (coe v8)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
