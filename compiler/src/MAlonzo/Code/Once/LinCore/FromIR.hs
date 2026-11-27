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

module MAlonzo.Code.Once.LinCore.FromIR where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.LinCore.Core
import qualified MAlonzo.Code.Once.LinCore.Flat
import qualified MAlonzo.Code.Once.LinCore.PassTr
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.LinCore.FromIR._._∋[_]_
d__'8715''91'_'93'__10 a0 a1 a2 a3 = ()
-- Once.LinCore.FromIR._.Cx
d_Cx_40 a0 = ()
-- Once.LinCore.FromIR._.Gr
d_Gr_52 a0 = ()
-- Once.LinCore.FromIR._.Kd
d_Kd_58 a0 = ()
-- Once.LinCore.FromIR._.LF
d_LF_66 a0 = ()
-- Once.LinCore.FromIR._.LF∙
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
-- Once.LinCore.FromIR._.LTy
d_LTy_72 a0 = ()
-- Once.LinCore.FromIR._.Sg
d_Sg_90 a0 = ()
-- Once.LinCore.FromIR._.Sig
d_Sig_94 a0 = ()
-- Once.LinCore.FromIR._.flat
d_flat_150 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
d_flat_150 ~v0 = du_flat_150
du_flat_150 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
du_flat_150 = coe MAlonzo.Code.Once.LinCore.Core.du_flat_606
-- Once.LinCore.FromIR._.⌜_⌝
d_'8988'_'8989'_400 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_'8988'_'8989'_400 ~v0 = du_'8988'_'8989'_400
du_'8988'_'8989'_400 ::
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
du_'8988'_'8989'_400
  = coe MAlonzo.Code.Once.LinCore.Core.du_'8988'_'8989'_532
-- Once.LinCore.FromIR._.Sg.cod
d_cod_598 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_cod_598 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_cod_724 (coe v0)
-- Once.LinCore.FromIR._.Sg.dom
d_dom_600 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_dom_600 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_dom_722 (coe v0)
-- Once.LinCore.FromIR._.Sg.env
d_env_602 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_env_602 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_env_720 (coe v0)
-- Once.LinCore.FromIR._.Sg.gr
d_gr_604 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156
d_gr_604 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_gr_718 (coe v0)
-- Once.LinCore.FromIR._.Sg.kd
d_kd_606 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Kd_150
d_kd_606 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_kd_716 (coe v0)
-- Once.LinCore.FromIR._.Sig.info
d_info_610 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_info_610 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_info_692 (coe v0)
-- Once.LinCore.FromIR._.Sig.sA
d_sA_612 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_sA_612 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_sA_688 (coe v0)
-- Once.LinCore.FromIR._.Sig.sB
d_sB_614 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_sB_614 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_sB_690 (coe v0)
-- Once.LinCore.FromIR.P.BlkIR
d_BlkIR_708 a0 a1 a2 a3 a4 = ()
-- Once.LinCore.FromIR.P.GdIR
d_GdIR_714 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_706 -> ()
d_GdIR_714 = erased
-- Once.LinCore.FromIR.P.IR
d_IR_716 a0 a1 a2 a3 = ()
-- Once.LinCore.FromIR.P.InS
d_InS_720 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_InS_720 ~v0 = du_InS_720
du_InS_720 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
du_InS_720 = coe MAlonzo.Code.Once.LinCore.PassTr.du_InS_1166
-- Once.LinCore.FromIR.P.Prog
d_Prog_726 a0 a1 = ()
-- Once.LinCore.FromIR.P.copyIn
d_copyIn_736 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_copyIn_736 ~v0 v1 v2 ~v3 v4 = du_copyIn_736 v1 v2 v4
du_copyIn_736 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_copyIn_736 v0 v1 v2
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
-- Once.LinCore.FromIR.P.dropl
d_dropl_740 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_dropl_740 ~v0 ~v1 ~v2 v3 = du_dropl_740 v3
du_dropl_740 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_dropl_740 v0
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
-- Once.LinCore.FromIR.P.inco
d_inco_790 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_inco_790 ~v0 = du_inco_790
du_inco_790 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_inco_790 v0 v1
  = coe MAlonzo.Code.Once.LinCore.PassTr.du_inco_1174 v1
-- Once.LinCore.FromIR.P.k-copyIn
d_k'45'copyIn_798 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'copyIn_798 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_k'45'copyIn_798 v5
du_k'45'copyIn_798 ::
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'copyIn_798 v0
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
-- Once.LinCore.FromIR.P.k-dropl
d_k'45'dropl_800 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'dropl_800 ~v0 ~v1 ~v2 ~v3 = du_k'45'dropl_800
du_k'45'dropl_800 :: MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'dropl_800
  = coe
      MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
      (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1200)
      (coe
         MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1182
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1246)
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1152))
-- Once.LinCore.FromIR.P.k-inco
d_k'45'inco_802 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'inco_802 ~v0 = du_k'45'inco_802
du_k'45'inco_802 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'inco_802 v0 v1
  = coe MAlonzo.Code.Once.LinCore.PassTr.du_k'45'inco_1182 v1
-- Once.LinCore.FromIR.P.k-mapL
d_k'45'mapL_804 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'mapL_804 ~v0 = du_k'45'mapL_804
du_k'45'mapL_804 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'mapL_804 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Once.LinCore.PassTr.du_k'45'mapL_1138 v4 v6
-- Once.LinCore.FromIR.P.k-withE
d_k'45'withE_806 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'withE_806 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_k'45'withE_806 v5
du_k'45'withE_806 ::
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'withE_806 v0
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
-- Once.LinCore.FromIR.P.mapL
d_mapL_808 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_mapL_808 ~v0 = du_mapL_808
du_mapL_808 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_mapL_808 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.LinCore.PassTr.du_mapL_1098 v3 v4 v5
-- Once.LinCore.FromIR.P.tr
d_tr_816 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_706 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_tr_816 ~v0 = du_tr_816
du_tr_816 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_706 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_tr_816 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.LinCore.PassTr.du_tr_1192 v1 v2 v3
-- Once.LinCore.FromIR.P.tr-blk
d_tr'45'blk_818 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_706 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_BlkIR_712 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_tr'45'blk_818 ~v0 = du_tr'45'blk_818
du_tr'45'blk_818 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_706 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_BlkIR_712 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_tr'45'blk_818 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.LinCore.PassTr.du_tr'45'blk_1202 v1 v2 v3 v4
-- Once.LinCore.FromIR.P.tr-def
d_tr'45'def_820 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_706 -> AgdaAny -> AgdaAny
d_tr'45'def_820 ~v0 = du_tr'45'def_820
du_tr'45'def_820 ::
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_706 -> AgdaAny -> AgdaAny
du_tr'45'def_820 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.LinCore.PassTr.du_tr'45'def_1306 v0 v2 v3 v4 v5
-- Once.LinCore.FromIR.P.tr-gd
d_tr'45'gd_822 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_706 -> AgdaAny -> AgdaAny
d_tr'45'gd_822 ~v0 = du_tr'45'gd_822
du_tr'45'gd_822 ::
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_706 -> AgdaAny -> AgdaAny
du_tr'45'gd_822 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.LinCore.PassTr.du_tr'45'gd_1216 v0 v2 v3 v4 v5 v6
-- Once.LinCore.FromIR.P.trP
d_trP_824 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_Prog_1280 ->
  MAlonzo.Code.Once.LinCore.Core.T_Defs_2238
d_trP_824 ~v0 = du_trP_824
du_trP_824 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_Prog_1280 ->
  MAlonzo.Code.Once.LinCore.Core.T_Defs_2238
du_trP_824 = coe MAlonzo.Code.Once.LinCore.PassTr.du_trP_1312
-- Once.LinCore.FromIR.P.withE
d_withE_826 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_withE_826 ~v0 v1 v2 ~v3 v4 = du_withE_826 v1 v2 v4
du_withE_826 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_withE_826 v0 v1 v2
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
-- Once.LinCore.FromIR.grade
d_grade_928 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156
d_grade_928 ~v0 v1 = du_grade_928 v1
du_grade_928 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156
du_grade_928 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v1
        -> coe MAlonzo.Code.Once.LinCore.Core.C_act_158
      MAlonzo.Code.Once.Spec.Grade.C_eff_44
        -> coe MAlonzo.Code.Once.LinCore.Core.C_eff_160
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.⟪_⟫
d_'10218'_'10219'_930 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_'10218'_'10219'_930 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe MAlonzo.Code.Once.LinCore.Core.C_One_180
      MAlonzo.Code.Once.IRTy.C_Void_18
        -> coe MAlonzo.Code.Once.LinCore.Core.C_Zero_182
      MAlonzo.Code.Once.IRTy.C__'42'__20 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
             (coe d_'10218'_'10219'_930 (coe v0) (coe v2))
             (coe d_'10218'_'10219'_930 (coe v0) (coe v3))
      MAlonzo.Code.Once.IRTy.C__'43'__22 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8853't__186
             (coe d_'10218'_'10219'_930 (coe v0) (coe v2))
             (coe d_'10218'_'10219'_930 (coe v0) (coe v3))
      MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_Fn_190
             (coe MAlonzo.Code.Once.LinCore.Core.C_many_154)
             (coe du_grade_928 (coe v3))
             (coe d_'10218'_'10219'_930 (coe v0) (coe v2))
             (coe d_'10218'_'10219'_930 (coe v0) (coe v4))
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v2
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_μt_194
             (coe d_lf_932 (coe v0) (coe v2))
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v2
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_Nu_192
             (coe d_lf_932 (coe v0) (coe v2))
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_Bt_196
             (coe MAlonzo.Code.Once.LinCore.Flat.C_int_48)
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_Bt_196
             (coe MAlonzo.Code.Once.LinCore.Flat.C_float_50)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.lf
d_lf_932 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134
d_lf_932 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_K_8 v2 -> coe d_lfK_934 (coe v0) (coe v2)
      MAlonzo.Code.Once.IRTy.C_Id_10
        -> coe MAlonzo.Code.Once.LinCore.Core.C_Idf_136
      MAlonzo.Code.Once.IRTy.C__'8853'__12 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8853'f__146
             (coe d_lf_932 (coe v0) (coe v2)) (coe d_lf_932 (coe v0) (coe v3))
      MAlonzo.Code.Once.IRTy.C__'8855'__14 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8855'f__148
             (coe d_lf_932 (coe v0) (coe v2)) (coe d_lf_932 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.lfK
d_lfK_934 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134
d_lfK_934 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe MAlonzo.Code.Once.LinCore.Core.C_Kone_138
      MAlonzo.Code.Once.IRTy.C_Void_18
        -> coe MAlonzo.Code.Once.LinCore.Core.C_Kzero_140
      MAlonzo.Code.Once.IRTy.C__'42'__20 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8855'f__148
             (coe d_lfK_934 (coe v0) (coe v2)) (coe d_lfK_934 (coe v0) (coe v3))
      MAlonzo.Code.Once.IRTy.C__'43'__22 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8853'f__146
             (coe d_lfK_934 (coe v0) (coe v2)) (coe d_lfK_934 (coe v0) (coe v3))
      MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24 v2 v3 v4
        -> coe MAlonzo.Code.Once.LinCore.Core.C_Kzero_140
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v2
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_Kμ_144
             (coe d_lf_932 (coe v0) (coe v2))
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v2
        -> coe MAlonzo.Code.Once.LinCore.Core.C_Kzero_140
      MAlonzo.Code.Once.IRTy.C_Int_30
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_Kb_142
             (coe MAlonzo.Code.Once.LinCore.Flat.C_int_48)
      MAlonzo.Code.Once.IRTy.C_Float_32
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_Kb_142
             (coe MAlonzo.Code.Once.LinCore.Flat.C_float_50)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.⟪⟫-K
d_'10218''10219''45'K_978 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IsBaseTypeI_110 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10218''10219''45'K_978 = erased
-- Once.LinCore.FromIR.⟪⟫-TI
d_'10218''10219''45'TI_1004 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_132 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10218''10219''45'TI_1004 = erased
-- Once.LinCore.FromIR.⟪⌊⌋⟫-flat
d_'10218''8970''8971''10219''45'flat_1028 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10218''8970''8971''10219''45'flat_1028 = erased
-- Once.LinCore.FromIR.blk?
d_blk'63'_1046 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_706 ->
  Maybe MAlonzo.Code.Once.LinCore.PassTr.T_BlkIR_712
d_blk'63'_1046 ~v0 ~v1 v2 v3 v4 = du_blk'63'_1046 v2 v3 v4
du_blk'63'_1046 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_706 ->
  Maybe MAlonzo.Code.Once.LinCore.PassTr.T_BlkIR_712
du_blk'63'_1046 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.LinCore.PassTr.C_id_722
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'id_864)
      MAlonzo.Code.Once.LinCore.PassTr.C__'8728'__730 v4 v6 v7
        -> coe
             MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
             (coe du_blk'63'_1046 (coe v4) (coe v1) (coe v6))
             (coe
                (\ v8 ->
                   coe
                     MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                     (coe du_blk'63'_1046 (coe v0) (coe v4) (coe v7))
                     (coe
                        (\ v9 ->
                           coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45''8728'_876 v8 v9)))))
      MAlonzo.Code.Once.LinCore.PassTr.C_'10216'_'44'_'10217'_738 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v8 v9
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe du_blk'63'_1046 (coe v0) (coe v8) (coe v6))
                    (coe
                       (\ v10 ->
                          coe
                            MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                            (coe du_blk'63'_1046 (coe v0) (coe v9) (coe v7))
                            (coe
                               (\ v11 ->
                                  coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe
                                       MAlonzo.Code.Once.LinCore.PassTr.C_i'45'pair_888 v10 v11)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.PassTr.C_fst_744
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'fst_894)
      MAlonzo.Code.Once.LinCore.PassTr.C_snd_750
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'snd_900)
      MAlonzo.Code.Once.LinCore.PassTr.C_inl_756
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'inl_906)
      MAlonzo.Code.Once.LinCore.PassTr.C_inr_762
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'inr_912)
      MAlonzo.Code.Once.LinCore.PassTr.C_case_770 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v8 v9
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe du_blk'63'_1046 (coe v8) (coe v1) (coe v6))
                    (coe
                       (\ v10 ->
                          coe
                            MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                            (coe du_blk'63'_1046 (coe v9) (coe v1) (coe v7))
                            (coe
                               (\ v11 ->
                                  coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe
                                       MAlonzo.Code.Once.LinCore.PassTr.C_i'45'case_924 v10 v11)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.PassTr.C_terminal_774
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'term_928)
      MAlonzo.Code.Once.LinCore.PassTr.C_initial_778
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'init_932)
      MAlonzo.Code.Once.LinCore.PassTr.C_curry_790 v7 v8
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'curry_946)
      MAlonzo.Code.Once.LinCore.PassTr.C_apply_798
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v8 v9 v10 v11
                      -> case coe v9 of
                           MAlonzo.Code.Once.LinCore.Core.C_act_158
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                  (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'apply_952)
                           MAlonzo.Code.Once.LinCore.Core.C_eff_160
                             -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.PassTr.C_In_802
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'In_956)
      MAlonzo.Code.Once.LinCore.PassTr.C_out'45'μ_806
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'out_960)
      MAlonzo.Code.Once.LinCore.PassTr.C_Cata_814 v6
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v7 v8
               -> case coe v8 of
                    MAlonzo.Code.Once.LinCore.Core.C_μt_194 v9
                      -> coe
                           MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                           (coe
                              du_blk'63'_1046
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 (coe v7)
                                 (coe
                                    MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198 (coe v9)
                                    (coe v1)))
                              (coe v1) (coe v6))
                           (coe
                              (\ v10 ->
                                 coe
                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                   (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'cata_970 v10)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.PassTr.C_Ana_824 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'ana_982)
      MAlonzo.Code.Once.LinCore.PassTr.C_Out_828
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'Out_986)
      MAlonzo.Code.Once.LinCore.PassTr.C_in'45'ν_832
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'inν_990)
      MAlonzo.Code.Once.LinCore.PassTr.C_Iter_842 v6 v7
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.LinCore.PassTr.C_const_846 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'const_996)
      MAlonzo.Code.Once.LinCore.PassTr.C_SigOp_850 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'op_1000)
      MAlonzo.Code.Once.LinCore.PassTr.C_Call_860 v3 v4 v7
        -> case coe v4 of
             MAlonzo.Code.Once.LinCore.Core.C_act_158
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'call_1010)
             MAlonzo.Code.Once.LinCore.Core.C_eff_160
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.gd?
d_gd'63'_1120 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_706 -> Maybe AgdaAny
d_gd'63'_1120 ~v0 ~v1 v2 v3 v4 v5 = du_gd'63'_1120 v2 v3 v4 v5
du_gd'63'_1120 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_706 -> Maybe AgdaAny
du_gd'63'_1120 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.LinCore.Core.C_act_158
        -> coe du_blk'63'_1046 (coe v0) (coe v1) (coe v3)
      MAlonzo.Code.Once.LinCore.Core.C_eff_160
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.Hit
d_Hit_1132 a0 a1 a2 a3 = ()
data T_Hit_1132
  = C_hit_1152 Integer MAlonzo.Code.Once.LinCore.Core.T_Gr_156
               MAlonzo.Code.Once.LinCore.Core.T__'8715''91'_'93'__738
-- Once.LinCore.FromIR.Hit.l
d_l_1146 :: T_Hit_1132 -> Integer
d_l_1146 v0
  = case coe v0 of
      C_hit_1152 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.Hit.g
d_g_1148 :: T_Hit_1132 -> MAlonzo.Code.Once.LinCore.Core.T_Gr_156
d_g_1148 v0
  = case coe v0 of
      C_hit_1152 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.Hit.p
d_p_1150 ::
  T_Hit_1132 ->
  MAlonzo.Code.Once.LinCore.Core.T__'8715''91'_'93'__738
d_p_1150 v0
  = case coe v0 of
      C_hit_1152 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.Resolver
d_Resolver_1154 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 -> ()
d_Resolver_1154 = erased
-- Once.LinCore.FromIR.unlinked-i
d_unlinked'45'i_1162 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_unlinked'45'i_1162 ~v0 = du_unlinked'45'i_1162
du_unlinked'45'i_1162 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
du_unlinked'45'i_1162
  = coe
      MAlonzo.Code.Once.SigOp.Info.C_mk'45'info''_124
      (coe
         MAlonzo.Code.Once.Spec.Name.C_canonical_12
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe ("Generators" :: Data.Text.Text))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe ("unlinked" :: Data.Text.Text))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
      (coe MAlonzo.Code.Once.SigOp.Info.C_haltsV_94)
      (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Unit_94)
      (coe MAlonzo.Code.Once.Spec.Type.C_b'45'Void_96)
-- Once.LinCore.FromIR.unlinked
d_unlinked_1170 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_706
d_unlinked_1170 ~v0 ~v1 ~v2 ~v3 = du_unlinked_1170
du_unlinked_1170 :: MAlonzo.Code.Once.LinCore.PassTr.T_IR_706
du_unlinked_1170
  = coe
      MAlonzo.Code.Once.LinCore.PassTr.C__'8728'__730
      (coe MAlonzo.Code.Once.LinCore.Core.C_Zero_182)
      (coe MAlonzo.Code.Once.LinCore.PassTr.C_initial_778)
      (coe
         MAlonzo.Code.Once.LinCore.PassTr.C__'8728'__730
         (coe
            MAlonzo.Code.Once.LinCore.Core.du_'8988'_'8989'_532
            (coe
               MAlonzo.Code.Once.LinCore.Core.du_sdom_696
               (coe
                  MAlonzo.Code.Once.LinCore.Core.C_sig_694
                  (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                  (coe MAlonzo.Code.Once.Spec.Type.C_Void_20)
                  (coe du_unlinked'45'i_1162))))
         (coe
            MAlonzo.Code.Once.LinCore.PassTr.C_SigOp_850
            (coe
               MAlonzo.Code.Once.LinCore.Core.C_sig_694
               (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
               (coe MAlonzo.Code.Once.Spec.Type.C_Void_20)
               (coe du_unlinked'45'i_1162)))
         (coe MAlonzo.Code.Once.LinCore.PassTr.C_terminal_774))
-- Once.LinCore.FromIR.callAt
d_callAt_1178 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Maybe T_Hit_1132 -> Maybe MAlonzo.Code.Once.LinCore.PassTr.T_IR_706
d_callAt_1178 ~v0 ~v1 ~v2 ~v3 v4 = du_callAt_1178 v4
du_callAt_1178 ::
  Maybe T_Hit_1132 -> Maybe MAlonzo.Code.Once.LinCore.PassTr.T_IR_706
du_callAt_1178 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             C_hit_1152 v2 v3 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe MAlonzo.Code.Once.LinCore.PassTr.C_Call_860 v2 v3 v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe du_unlinked_1170)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR._.trI
d_trI_1196 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1132) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.LinCore.PassTr.T_IR_706
d_trI_1196 v0 ~v1 v2 v3 v4 v5 = du_trI_1196 v0 v2 v3 v4 v5
du_trI_1196 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1132) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.LinCore.PassTr.T_IR_706
du_trI_1196 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_id_722)
      MAlonzo.Code.Once.IR.C__'8728'__28 v6 v8 v9
        -> coe
             MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
             (coe du_trI_1196 (coe v0) (coe v1) (coe v6) (coe v3) (coe v8))
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                     (coe du_trI_1196 (coe v0) (coe v1) (coe v2) (coe v6) (coe v9))
                     (coe
                        (\ v11 ->
                           coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe
                                MAlonzo.Code.Once.LinCore.PassTr.C__'8728'__730
                                (d_'10218'_'10219'_930 (coe v0) (coe v6)) v10 v11)))))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v8 v9
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe du_trI_1196 (coe v0) (coe v1) (coe v2) (coe v10) (coe v8))
                    (coe
                       (\ v12 ->
                          coe
                            MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                            (coe du_trI_1196 (coe v0) (coe v1) (coe v2) (coe v11) (coe v9))
                            (coe
                               (\ v13 ->
                                  coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe
                                       MAlonzo.Code.Once.LinCore.PassTr.C_'10216'_'44'_'10217'_738
                                       v12 v13)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_fst_744)
      MAlonzo.Code.Once.IR.C_snd_48
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_snd_750)
      MAlonzo.Code.Once.IR.C_inl_54
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_inl_756)
      MAlonzo.Code.Once.IR.C_inr_60
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_inr_762)
      MAlonzo.Code.Once.IR.C_case_68 v8 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v10 v11
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe du_trI_1196 (coe v0) (coe v1) (coe v10) (coe v3) (coe v8))
                    (coe
                       (\ v12 ->
                          coe
                            MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                            (coe du_trI_1196 (coe v0) (coe v1) (coe v11) (coe v3) (coe v9))
                            (coe
                               (\ v13 ->
                                  coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe MAlonzo.Code.Once.LinCore.PassTr.C_case_770 v12 v13)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_terminal_774)
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_initial_778)
      MAlonzo.Code.Once.IR.C_curry_86 v9
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24 v10 v11 v12
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe
                       du_trI_1196 (coe v0) (coe v1)
                       (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v2) (coe v10))
                       (coe v12) (coe v9))
                    (coe
                       (\ v13 ->
                          coe
                            MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                            (coe
                               du_gd'63'_1120
                               (coe
                                  d_'10218'_'10219'_930 (coe v0)
                                  (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v2) (coe v10)))
                               (coe d_'10218'_'10219'_930 (coe v0) (coe v12))
                               (coe du_grade_928 (coe v11)) (coe v13))
                            (coe
                               (\ v14 ->
                                  coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe MAlonzo.Code.Once.LinCore.PassTr.C_curry_790 v13 v14)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_94
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_apply_798)
      MAlonzo.Code.Once.IR.C_In_98 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_In_802)
      MAlonzo.Code.Once.IR.C_out'45'μ_102 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_out'45'μ_806)
      MAlonzo.Code.Once.IR.C_Cata_110 v6 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> case coe v11 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v12
                      -> coe
                           MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                           (coe
                              du_trI_1196 (coe v0) (coe v1)
                              (coe
                                 MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v10)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90 (coe v12)
                                    (coe v3)))
                              (coe v3) (coe v9))
                           (coe
                              (\ v13 ->
                                 coe
                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                   (coe MAlonzo.Code.Once.LinCore.PassTr.C_Cata_814 v13)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_114 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_Out_828)
      MAlonzo.Code.Once.IR.C_in'45'ν_118 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_in'45'ν_832)
      MAlonzo.Code.Once.IR.C_Ana_126 v6 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> case coe v3 of
                    MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v12
                      -> coe
                           MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                           (coe
                              du_trI_1196 (coe v0) (coe v1) (coe v2)
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90 (coe v12) (coe v11))
                              (coe v9))
                           (coe
                              (\ v13 ->
                                 coe
                                   MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                                   (coe
                                      du_blk'63'_1046
                                      (coe
                                         MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                                         (coe d_'10218'_'10219'_930 (coe v0) (coe v10))
                                         (coe d_'10218'_'10219'_930 (coe v0) (coe v11)))
                                      (coe
                                         MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198
                                         (coe d_lf_932 (coe v0) (coe v12))
                                         (coe d_'10218'_'10219'_930 (coe v0) (coe v11)))
                                      (coe v13))
                                   (coe
                                      (\ v14 ->
                                         coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe
                                              MAlonzo.Code.Once.LinCore.PassTr.C_Ana_824 v13
                                              v14)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Iter_134 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe
                       du_trI_1196 (coe v0) (coe v1) (coe v2)
                       (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v3) (coe v10))
                       (coe v8))
                    (coe
                       (\ v11 ->
                          coe
                            MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                            (coe
                               du_blk'63'_1046 (coe d_'10218'_'10219'_930 (coe v0) (coe v2))
                               (coe
                                  d_'10218'_'10219'_930 (coe v0)
                                  (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v3) (coe v10)))
                               (coe v11))
                            (coe
                               (\ v12 ->
                                  coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe MAlonzo.Code.Once.LinCore.PassTr.C_Iter_842 v11 v12)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_138 v6 v7
        -> coe
             seq (coe v6)
             (coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Once.LinCore.PassTr.C_const_846 v7))
      MAlonzo.Code.Once.IR.C_SigOp_144 v5 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Once.LinCore.PassTr.C_SigOp_850
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_sig_694 (coe v5) (coe v6)
                   (coe v7)))
      MAlonzo.Code.Once.IR.C_Call_150 v7
        -> coe du_callAt_1178 (coe v1 v7 v2 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.TrProg
d_TrProg_1310 a0 = ()
data T_TrProg_1310
  = C_trProg_1324 MAlonzo.Code.Once.LinCore.Core.T_Cx_728
                  MAlonzo.Code.Once.LinCore.PassTr.T_Prog_1280
                  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
                   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
                   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1132)
-- Once.LinCore.FromIR.TrProg.Γ
d_Γ_1318 ::
  T_TrProg_1310 -> MAlonzo.Code.Once.LinCore.Core.T_Cx_728
d_Γ_1318 v0
  = case coe v0 of
      C_trProg_1324 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.TrProg.prog
d_prog_1320 ::
  T_TrProg_1310 -> MAlonzo.Code.Once.LinCore.PassTr.T_Prog_1280
d_prog_1320 v0
  = case coe v0 of
      C_trProg_1324 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.TrProg.rs
d_rs_1322 ::
  T_TrProg_1310 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1132
d_rs_1322 v0
  = case coe v0 of
      C_trProg_1324 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.weaken
d_weaken_1334 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_Hit_1132 -> T_Hit_1132
d_weaken_1334 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_weaken_1334 v5
du_weaken_1334 :: T_Hit_1132 -> T_Hit_1132
du_weaken_1334 v0
  = case coe v0 of
      C_hit_1152 v1 v2 v3
        -> coe
             C_hit_1152 (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.LinCore.Core.C_there_754 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.extend-at
d_extend'45'at_1354 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1132) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_Hit_1132
d_extend'45'at_1354 ~v0 v1 v2 v3 ~v4 v5 v6 v7 v8 v9 v10
  = du_extend'45'at_1354 v1 v2 v3 v5 v6 v7 v8 v9 v10
du_extend'45'at_1354 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1132) ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_Hit_1132
du_extend'45'at_1354 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v6 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
        -> if coe v9
             then coe
                    seq (coe v10)
                    (case coe v7 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                         -> if coe v11
                              then coe
                                     seq (coe v12)
                                     (case coe v8 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                          -> if coe v13
                                               then coe
                                                      seq (coe v14)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                         (coe
                                                            C_hit_1152
                                                            (coe
                                                               MAlonzo.Code.Once.LinCore.Core.du_len_734
                                                               (coe v0))
                                                            (coe v1)
                                                            (coe
                                                               MAlonzo.Code.Once.LinCore.Core.C_here_744)))
                                               else coe
                                                      seq (coe v14)
                                                      (coe
                                                         MAlonzo.Code.Data.Maybe.Base.du_map_64
                                                         (coe du_weaken_1334) (coe v2 v3 v4 v5))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              else coe
                                     seq (coe v12)
                                     (coe
                                        MAlonzo.Code.Data.Maybe.Base.du_map_64 (coe du_weaken_1334)
                                        (coe v2 v3 v4 v5))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v10)
                    (coe
                       MAlonzo.Code.Data.Maybe.Base.du_map_64 (coe du_weaken_1334)
                       (coe v2 v3 v4 v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.extend
d_extend_1420 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1132) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1132
d_extend_1420 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_extend_1420 v1 v2 v3 v4 v5 v6 v7
du_extend_1420 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1132) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1132
du_extend_1420 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_extend'45'at_1354 (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
      (coe v6)
      (coe
         MAlonzo.Code.Once.CanonicalName.d__'8799''7580'__4
         (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v3))
         (coe v4))
      (coe
         MAlonzo.Code.Once.IRTy.d__'8799'IRTy__232
         (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v3))
         (coe v5))
      (coe
         MAlonzo.Code.Once.IRTy.d__'8799'IRTy__232
         (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v3))
         (coe v6))
-- Once.LinCore.FromIR.entry-at
d_entry'45'at_1440 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_Prog_1280 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1132) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_706 ->
  Maybe MAlonzo.Code.Once.LinCore.PassTr.T_BlkIR_712 -> T_TrProg_1310
d_entry'45'at_1440 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> coe
             C_trProg_1324
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'9656'__732 (coe v1)
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_sg_726
                   (coe MAlonzo.Code.Once.LinCore.Core.C_once_152)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_act_158)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                   (coe
                      d_'10218'_'10219'_930 (coe v0)
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v4)))
                   (coe
                      d_'10218'_'10219'_930 (coe v0)
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v4)))))
             (coe
                MAlonzo.Code.Once.LinCore.PassTr.C__'9657'_'8739'__1294 v2 v5 v7)
             (coe
                du_extend_1420 (coe v1)
                (coe MAlonzo.Code.Once.LinCore.Core.C_act_158) (coe v3) (coe v4))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             C_trProg_1324
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'9656'__732 (coe v1)
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_sg_726
                   (coe MAlonzo.Code.Once.LinCore.Core.C_once_152)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_eff_160)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                   (coe
                      d_'10218'_'10219'_930 (coe v0)
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v4)))
                   (coe
                      d_'10218'_'10219'_930 (coe v0)
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v4)))))
             (coe
                MAlonzo.Code.Once.LinCore.PassTr.C__'9657'_'8739'__1294 v2 v5
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             (coe
                du_extend_1420 (coe v1)
                (coe MAlonzo.Code.Once.LinCore.Core.C_eff_160) (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.entry
d_entry_1464 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_Prog_1280 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1132) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_706 -> T_TrProg_1310
d_entry_1464 v0 v1 v2 v3 v4 v5
  = coe
      d_entry'45'at_1440 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5)
      (coe
         du_blk'63'_1046
         (coe
            d_'10218'_'10219'_930 (coe v0)
            (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v4)))
         (coe
            d_'10218'_'10219'_930 (coe v0)
            (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v4)))
         (coe v5))
-- Once.LinCore.FromIR.trTable
d_trTable_1474 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Maybe T_TrProg_1310
d_trTable_1474 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_trProg_1324 (coe MAlonzo.Code.Once.LinCore.Core.C_ε_730)
                (coe MAlonzo.Code.Once.LinCore.PassTr.C_ε_1282)
                (coe
                   (\ v2 v3 v4 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
             (coe d_trTable_1474 (coe v0) (coe v3))
             (coe
                (\ v4 ->
                   coe
                     MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                     (coe
                        du_trI_1196 (coe v0) (coe d_rs_1322 (coe v4))
                        (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                        (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                        (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2)))
                     (coe
                        (\ v5 ->
                           coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe
                                d_entry_1464 (coe v0) (coe d_Γ_1318 (coe v4))
                                (coe d_prog_1320 (coe v4)) (coe d_rs_1322 (coe v4)) (coe v2)
                                (coe v5))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR._.Tr
d_Tr_1502 a0 a1 a2 a3 a4 a5 a6 = ()
data T_Tr_1502
  = C_t'45'id_1506 | C_t'45''8728'_1522 T_Tr_1502 T_Tr_1502 |
    C_t'45'pair_1538 T_Tr_1502 T_Tr_1502 | C_t'45'fst_1544 |
    C_t'45'snd_1550 | C_t'45'inl_1556 | C_t'45'inr_1562 |
    C_t'45'case_1578 T_Tr_1502 T_Tr_1502 | C_t'45'term_1582 |
    C_t'45'init_1586 | C_t'45'curry_1602 T_Tr_1502 |
    C_t'45'apply_1610 | C_t'45'In_1618 | C_t'45'out_1626 |
    C_t'45'cata_1642 MAlonzo.Code.Once.LinCore.PassTr.T_IR_706
                     T_Tr_1502 |
    C_t'45'Out_1650 | C_t'45'inν_1658 |
    C_t'45'ana_1676 MAlonzo.Code.Once.LinCore.PassTr.T_IR_706
                    T_Tr_1502 |
    C_t'45'iter_1690 T_Tr_1502 | C_t'45'int_1694 | C_t'45'float_1698 |
    C_t'45'op_1706 | C_t'45'hit_1720 | C_t'45'miss_1728
-- Once.LinCore.FromIR._.bind-just
d_bind'45'just_1742 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1132) ->
  () ->
  () ->
  Maybe AgdaAny ->
  (AgdaAny -> Maybe AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bind'45'just_1742 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8
  = du_bind'45'just_1742 v5 v8
du_bind'45'just_1742 ::
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bind'45'just_1742 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR._.trI-Tr
d_trI'45'Tr_1756 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1132) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_706 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_Tr_1502
d_trI'45'Tr_1756 v0 ~v1 v2 v3 v4 v5 ~v6 ~v7
  = du_trI'45'Tr_1756 v0 v2 v3 v4 v5
du_trI'45'Tr_1756 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1132) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_Tr_1502
du_trI'45'Tr_1756 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_t'45'id_1506
      MAlonzo.Code.Once.IR.C__'8728'__28 v6 v8 v9
        -> coe
             C_t'45''8728'_1522
             (coe
                du_trI'45'Tr_1756 (coe v0) (coe v1) (coe v6) (coe v3) (coe v8))
             (coe
                du_trI'45'Tr_1756 (coe v0) (coe v1) (coe v2) (coe v6) (coe v9))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v8 v9
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> coe
                    C_t'45'pair_1538
                    (coe
                       du_trI'45'Tr_1756 (coe v0) (coe v1) (coe v2) (coe v10) (coe v8))
                    (coe
                       du_trI'45'Tr_1756 (coe v0) (coe v1) (coe v2) (coe v11) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_t'45'fst_1544
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_t'45'snd_1550
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_t'45'inl_1556
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_t'45'inr_1562
      MAlonzo.Code.Once.IR.C_case_68 v8 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v10 v11
               -> coe
                    C_t'45'case_1578
                    (coe
                       du_trI'45'Tr_1756 (coe v0) (coe v1) (coe v10) (coe v3) (coe v8))
                    (coe
                       du_trI'45'Tr_1756 (coe v0) (coe v1) (coe v11) (coe v3) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_t'45'term_1582
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_t'45'init_1586
      MAlonzo.Code.Once.IR.C_curry_86 v9
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24 v10 v11 v12
               -> coe
                    C_t'45'curry_1602
                    (coe
                       du_trI'45'Tr_1756 (coe v0) (coe v1)
                       (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v2) (coe v10))
                       (coe v12) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_94 -> coe C_t'45'apply_1610
      MAlonzo.Code.Once.IR.C_In_98 v6 -> coe C_t'45'In_1618
      MAlonzo.Code.Once.IR.C_out'45'μ_102 v6 -> coe C_t'45'out_1626
      MAlonzo.Code.Once.IR.C_Cata_110 v6 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> case coe v11 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v12
                      -> coe
                           C_t'45'cata_1642
                           (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 du_bind'45'just_1742
                                 (coe
                                    du_trI_1196 (coe v0) (coe v1)
                                    (coe
                                       MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v10)
                                       (coe
                                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90 (coe v12)
                                          (coe v3)))
                                    (coe v3) (coe v9))
                                 erased))
                           (coe
                              du_trI'45'Tr_1756 (coe v0) (coe v1)
                              (coe
                                 MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v10)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90 (coe v12)
                                    (coe v3)))
                              (coe v3) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_114 v6 -> coe C_t'45'Out_1650
      MAlonzo.Code.Once.IR.C_in'45'ν_118 v6 -> coe C_t'45'inν_1658
      MAlonzo.Code.Once.IR.C_Ana_126 v6 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> case coe v3 of
                    MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v12
                      -> coe
                           C_t'45'ana_1676
                           (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 du_bind'45'just_1742
                                 (coe
                                    du_trI_1196 (coe v0) (coe v1) (coe v2)
                                    (coe
                                       MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90 (coe v12)
                                       (coe v11))
                                    (coe v9))
                                 erased))
                           (coe
                              du_trI'45'Tr_1756 (coe v0) (coe v1) (coe v2)
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90 (coe v12) (coe v11))
                              (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Iter_134 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
               -> coe
                    C_t'45'iter_1690
                    (coe
                       du_trI'45'Tr_1756 (coe v0) (coe v1) (coe v2)
                       (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v3) (coe v10))
                       (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_138 v6 v7
        -> case coe v6 of
             MAlonzo.Code.Once.IRTy.C_fits'45'int_516 -> coe C_t'45'int_1694
             MAlonzo.Code.Once.IRTy.C_fits'45'float_518 -> coe C_t'45'float_1698
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_SigOp_144 v5 v6 v7 -> coe C_t'45'op_1706
      MAlonzo.Code.Once.IR.C_Call_150 v7
        -> coe du_call'45'tr_1912 (coe v1 v7 v2 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR._._.call-tr
d_call'45'tr_1912 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1132) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_706 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe T_Hit_1132 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_706 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_Tr_1502
d_call'45'tr_1912 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
  = du_call'45'tr_1912 v8
du_call'45'tr_1912 :: Maybe T_Hit_1132 -> T_Tr_1502
du_call'45'tr_1912 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe seq (coe v1) (coe C_t'45'hit_1720)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe C_t'45'miss_1728
      _ -> MAlonzo.RTE.mazUnreachableError
