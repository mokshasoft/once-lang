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
d_Sg_88 a0 = ()
-- Once.LinCore.FromIR._.Sig
d_Sig_92 a0 = ()
-- Once.LinCore.FromIR._.flat
d_flat_148 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
d_flat_148 ~v0 = du_flat_148
du_flat_148 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
du_flat_148 = coe MAlonzo.Code.Once.LinCore.Core.du_flat_606
-- Once.LinCore.FromIR._.⌜_⌝
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
-- Once.LinCore.FromIR._.Sg.cod
d_cod_542 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_cod_542 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_cod_724 (coe v0)
-- Once.LinCore.FromIR._.Sg.dom
d_dom_544 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_dom_544 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_dom_722 (coe v0)
-- Once.LinCore.FromIR._.Sg.env
d_env_546 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_env_546 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_env_720 (coe v0)
-- Once.LinCore.FromIR._.Sg.gr
d_gr_548 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156
d_gr_548 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_gr_718 (coe v0)
-- Once.LinCore.FromIR._.Sg.kd
d_kd_550 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Kd_150
d_kd_550 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_kd_716 (coe v0)
-- Once.LinCore.FromIR._.Sig.info
d_info_554 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_info_554 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_info_692 (coe v0)
-- Once.LinCore.FromIR._.Sig.sA
d_sA_556 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_sA_556 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_sA_688 (coe v0)
-- Once.LinCore.FromIR._.Sig.sB
d_sB_558 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_sB_558 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_sB_690 (coe v0)
-- Once.LinCore.FromIR.P.BlkIR
d_BlkIR_652 a0 a1 a2 a3 a4 = ()
-- Once.LinCore.FromIR.P.GdIR
d_GdIR_658 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_650 -> ()
d_GdIR_658 = erased
-- Once.LinCore.FromIR.P.IR
d_IR_660 a0 a1 a2 a3 = ()
-- Once.LinCore.FromIR.P.InS
d_InS_664 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_InS_664 ~v0 = du_InS_664
du_InS_664 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
du_InS_664 = coe MAlonzo.Code.Once.LinCore.PassTr.du_InS_1110
-- Once.LinCore.FromIR.P.Prog
d_Prog_670 a0 a1 = ()
-- Once.LinCore.FromIR.P.copyIn
d_copyIn_680 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_copyIn_680 ~v0 v1 v2 ~v3 v4 = du_copyIn_680 v1 v2 v4
du_copyIn_680 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_copyIn_680 v0 v1 v2
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
d_dropl_684 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_dropl_684 ~v0 ~v1 ~v2 v3 = du_dropl_684 v3
du_dropl_684 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_dropl_684 v0
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
d_inco_734 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_inco_734 ~v0 = du_inco_734
du_inco_734 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_inco_734 v0 v1
  = coe MAlonzo.Code.Once.LinCore.PassTr.du_inco_1118 v1
-- Once.LinCore.FromIR.P.k-copyIn
d_k'45'copyIn_742 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'copyIn_742 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_k'45'copyIn_742 v5
du_k'45'copyIn_742 ::
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'copyIn_742 v0
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
d_k'45'dropl_744 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'dropl_744 ~v0 ~v1 ~v2 ~v3 = du_k'45'dropl_744
du_k'45'dropl_744 :: MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'dropl_744
  = coe
      MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
      (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1200)
      (coe
         MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1182
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1246)
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1152))
-- Once.LinCore.FromIR.P.k-inco
d_k'45'inco_746 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'inco_746 ~v0 = du_k'45'inco_746
du_k'45'inco_746 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'inco_746 v0 v1
  = coe MAlonzo.Code.Once.LinCore.PassTr.du_k'45'inco_1126 v1
-- Once.LinCore.FromIR.P.k-mapL
d_k'45'mapL_748 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'mapL_748 ~v0 = du_k'45'mapL_748
du_k'45'mapL_748 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'mapL_748 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Once.LinCore.PassTr.du_k'45'mapL_1082 v4 v6
-- Once.LinCore.FromIR.P.k-withE
d_k'45'withE_750 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'withE_750 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_k'45'withE_750 v5
du_k'45'withE_750 ::
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'withE_750 v0
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
d_mapL_752 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_mapL_752 ~v0 = du_mapL_752
du_mapL_752 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_mapL_752 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.LinCore.PassTr.du_mapL_1042 v3 v4 v5
-- Once.LinCore.FromIR.P.tr
d_tr_760 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_650 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_tr_760 ~v0 = du_tr_760
du_tr_760 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_650 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_tr_760 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.LinCore.PassTr.du_tr_1136 v1 v2 v3
-- Once.LinCore.FromIR.P.tr-blk
d_tr'45'blk_762 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_650 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_BlkIR_656 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_tr'45'blk_762 ~v0 = du_tr'45'blk_762
du_tr'45'blk_762 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_650 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_BlkIR_656 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_tr'45'blk_762 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.LinCore.PassTr.du_tr'45'blk_1146 v1 v2 v3 v4
-- Once.LinCore.FromIR.P.tr-def
d_tr'45'def_764 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_650 -> AgdaAny -> AgdaAny
d_tr'45'def_764 ~v0 = du_tr'45'def_764
du_tr'45'def_764 ::
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_650 -> AgdaAny -> AgdaAny
du_tr'45'def_764 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.LinCore.PassTr.du_tr'45'def_1250 v0 v2 v3 v4 v5
-- Once.LinCore.FromIR.P.tr-gd
d_tr'45'gd_766 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_650 -> AgdaAny -> AgdaAny
d_tr'45'gd_766 ~v0 = du_tr'45'gd_766
du_tr'45'gd_766 ::
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_650 -> AgdaAny -> AgdaAny
du_tr'45'gd_766 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.LinCore.PassTr.du_tr'45'gd_1160 v0 v2 v3 v4 v5 v6
-- Once.LinCore.FromIR.P.trP
d_trP_768 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_Prog_1224 ->
  MAlonzo.Code.Once.LinCore.Core.T_Defs_1832
d_trP_768 ~v0 = du_trP_768
du_trP_768 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_Prog_1224 ->
  MAlonzo.Code.Once.LinCore.Core.T_Defs_1832
du_trP_768 = coe MAlonzo.Code.Once.LinCore.PassTr.du_trP_1256
-- Once.LinCore.FromIR.P.withE
d_withE_770 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_withE_770 ~v0 v1 v2 ~v3 v4 = du_withE_770 v1 v2 v4
du_withE_770 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_withE_770 v0 v1 v2
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
d_grade_872 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156
d_grade_872 ~v0 v1 = du_grade_872 v1
du_grade_872 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156
du_grade_872 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v1
        -> coe MAlonzo.Code.Once.LinCore.Core.C_act_158
      MAlonzo.Code.Once.Spec.Grade.C_eff_44
        -> coe MAlonzo.Code.Once.LinCore.Core.C_eff_160
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.⟪_⟫
d_'10218'_'10219'_874 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_'10218'_'10219'_874 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe MAlonzo.Code.Once.LinCore.Core.C_One_180
      MAlonzo.Code.Once.IRTy.C_Void_18
        -> coe MAlonzo.Code.Once.LinCore.Core.C_Zero_182
      MAlonzo.Code.Once.IRTy.C__'42'__20 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
             (coe d_'10218'_'10219'_874 (coe v0) (coe v2))
             (coe d_'10218'_'10219'_874 (coe v0) (coe v3))
      MAlonzo.Code.Once.IRTy.C__'43'__22 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8853't__186
             (coe d_'10218'_'10219'_874 (coe v0) (coe v2))
             (coe d_'10218'_'10219'_874 (coe v0) (coe v3))
      MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_Fn_190
             (coe MAlonzo.Code.Once.LinCore.Core.C_many_154)
             (coe du_grade_872 (coe v3))
             (coe d_'10218'_'10219'_874 (coe v0) (coe v2))
             (coe d_'10218'_'10219'_874 (coe v0) (coe v4))
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v2
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_μt_194
             (coe d_lf_876 (coe v0) (coe v2))
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v2
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_Nu_192
             (coe d_lf_876 (coe v0) (coe v2))
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
d_lf_876 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134
d_lf_876 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_K_8 v2 -> coe d_lfK_878 (coe v0) (coe v2)
      MAlonzo.Code.Once.IRTy.C_Id_10
        -> coe MAlonzo.Code.Once.LinCore.Core.C_Idf_136
      MAlonzo.Code.Once.IRTy.C__'8853'__12 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8853'f__146
             (coe d_lf_876 (coe v0) (coe v2)) (coe d_lf_876 (coe v0) (coe v3))
      MAlonzo.Code.Once.IRTy.C__'8855'__14 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8855'f__148
             (coe d_lf_876 (coe v0) (coe v2)) (coe d_lf_876 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.lfK
d_lfK_878 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134
d_lfK_878 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe MAlonzo.Code.Once.LinCore.Core.C_Kone_138
      MAlonzo.Code.Once.IRTy.C_Void_18
        -> coe MAlonzo.Code.Once.LinCore.Core.C_Kzero_140
      MAlonzo.Code.Once.IRTy.C__'42'__20 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8855'f__148
             (coe d_lfK_878 (coe v0) (coe v2)) (coe d_lfK_878 (coe v0) (coe v3))
      MAlonzo.Code.Once.IRTy.C__'43'__22 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8853'f__146
             (coe d_lfK_878 (coe v0) (coe v2)) (coe d_lfK_878 (coe v0) (coe v3))
      MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24 v2 v3 v4
        -> coe MAlonzo.Code.Once.LinCore.Core.C_Kzero_140
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v2
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_Kμ_144
             (coe d_lf_876 (coe v0) (coe v2))
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
d_'10218''10219''45'K_922 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IsBaseTypeI_110 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10218''10219''45'K_922 = erased
-- Once.LinCore.FromIR.⟪⟫-TI
d_'10218''10219''45'TI_948 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_132 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10218''10219''45'TI_948 = erased
-- Once.LinCore.FromIR.⟪⌊⌋⟫-flat
d_'10218''8970''8971''10219''45'flat_972 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10218''8970''8971''10219''45'flat_972 = erased
-- Once.LinCore.FromIR.blk?
d_blk'63'_990 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_650 ->
  Maybe MAlonzo.Code.Once.LinCore.PassTr.T_BlkIR_656
d_blk'63'_990 ~v0 ~v1 v2 v3 v4 = du_blk'63'_990 v2 v3 v4
du_blk'63'_990 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_650 ->
  Maybe MAlonzo.Code.Once.LinCore.PassTr.T_BlkIR_656
du_blk'63'_990 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.LinCore.PassTr.C_id_666
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'id_808)
      MAlonzo.Code.Once.LinCore.PassTr.C__'8728'__674 v4 v6 v7
        -> coe
             MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
             (coe du_blk'63'_990 (coe v4) (coe v1) (coe v6))
             (coe
                (\ v8 ->
                   coe
                     MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                     (coe du_blk'63'_990 (coe v0) (coe v4) (coe v7))
                     (coe
                        (\ v9 ->
                           coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45''8728'_820 v8 v9)))))
      MAlonzo.Code.Once.LinCore.PassTr.C_'10216'_'44'_'10217'_682 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v8 v9
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe du_blk'63'_990 (coe v0) (coe v8) (coe v6))
                    (coe
                       (\ v10 ->
                          coe
                            MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                            (coe du_blk'63'_990 (coe v0) (coe v9) (coe v7))
                            (coe
                               (\ v11 ->
                                  coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe
                                       MAlonzo.Code.Once.LinCore.PassTr.C_i'45'pair_832 v10 v11)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.PassTr.C_fst_688
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'fst_838)
      MAlonzo.Code.Once.LinCore.PassTr.C_snd_694
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'snd_844)
      MAlonzo.Code.Once.LinCore.PassTr.C_inl_700
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'inl_850)
      MAlonzo.Code.Once.LinCore.PassTr.C_inr_706
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'inr_856)
      MAlonzo.Code.Once.LinCore.PassTr.C_case_714 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v8 v9
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe du_blk'63'_990 (coe v8) (coe v1) (coe v6))
                    (coe
                       (\ v10 ->
                          coe
                            MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                            (coe du_blk'63'_990 (coe v9) (coe v1) (coe v7))
                            (coe
                               (\ v11 ->
                                  coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe
                                       MAlonzo.Code.Once.LinCore.PassTr.C_i'45'case_868 v10 v11)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.PassTr.C_terminal_718
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'term_872)
      MAlonzo.Code.Once.LinCore.PassTr.C_initial_722
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'init_876)
      MAlonzo.Code.Once.LinCore.PassTr.C_curry_734 v7 v8
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'curry_890)
      MAlonzo.Code.Once.LinCore.PassTr.C_apply_742
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v8 v9 v10 v11
                      -> case coe v9 of
                           MAlonzo.Code.Once.LinCore.Core.C_act_158
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                  (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'apply_896)
                           MAlonzo.Code.Once.LinCore.Core.C_eff_160
                             -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.PassTr.C_In_746
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'In_900)
      MAlonzo.Code.Once.LinCore.PassTr.C_out'45'μ_750
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'out_904)
      MAlonzo.Code.Once.LinCore.PassTr.C_Cata_758 v6
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v7 v8
               -> case coe v8 of
                    MAlonzo.Code.Once.LinCore.Core.C_μt_194 v9
                      -> coe
                           MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                           (coe
                              du_blk'63'_990
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
                                   (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'cata_914 v10)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.PassTr.C_Ana_768 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'ana_926)
      MAlonzo.Code.Once.LinCore.PassTr.C_Out_772
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'Out_930)
      MAlonzo.Code.Once.LinCore.PassTr.C_in'45'ν_776
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'inν_934)
      MAlonzo.Code.Once.LinCore.PassTr.C_Iter_786 v6 v7
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.LinCore.PassTr.C_const_790 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'const_940)
      MAlonzo.Code.Once.LinCore.PassTr.C_SigOp_794 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'op_944)
      MAlonzo.Code.Once.LinCore.PassTr.C_Call_804 v3 v4 v7
        -> case coe v4 of
             MAlonzo.Code.Once.LinCore.Core.C_act_158
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'call_954)
             MAlonzo.Code.Once.LinCore.Core.C_eff_160
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.gd?
d_gd'63'_1064 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_650 -> Maybe AgdaAny
d_gd'63'_1064 ~v0 ~v1 v2 v3 v4 v5 = du_gd'63'_1064 v2 v3 v4 v5
du_gd'63'_1064 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_650 -> Maybe AgdaAny
du_gd'63'_1064 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.LinCore.Core.C_act_158
        -> coe du_blk'63'_990 (coe v0) (coe v1) (coe v3)
      MAlonzo.Code.Once.LinCore.Core.C_eff_160
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.Hit
d_Hit_1076 a0 a1 a2 a3 = ()
data T_Hit_1076
  = C_hit_1096 Integer MAlonzo.Code.Once.LinCore.Core.T_Gr_156
               MAlonzo.Code.Once.LinCore.Core.T__'8715''91'_'93'__738
-- Once.LinCore.FromIR.Hit.l
d_l_1090 :: T_Hit_1076 -> Integer
d_l_1090 v0
  = case coe v0 of
      C_hit_1096 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.Hit.g
d_g_1092 :: T_Hit_1076 -> MAlonzo.Code.Once.LinCore.Core.T_Gr_156
d_g_1092 v0
  = case coe v0 of
      C_hit_1096 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.Hit.p
d_p_1094 ::
  T_Hit_1076 ->
  MAlonzo.Code.Once.LinCore.Core.T__'8715''91'_'93'__738
d_p_1094 v0
  = case coe v0 of
      C_hit_1096 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.Resolver
d_Resolver_1098 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 -> ()
d_Resolver_1098 = erased
-- Once.LinCore.FromIR.unlinked-i
d_unlinked'45'i_1106 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_unlinked'45'i_1106 ~v0 = du_unlinked'45'i_1106
du_unlinked'45'i_1106 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
du_unlinked'45'i_1106
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
d_unlinked_1114 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_650
d_unlinked_1114 ~v0 ~v1 ~v2 ~v3 = du_unlinked_1114
du_unlinked_1114 :: MAlonzo.Code.Once.LinCore.PassTr.T_IR_650
du_unlinked_1114
  = coe
      MAlonzo.Code.Once.LinCore.PassTr.C__'8728'__674
      (coe MAlonzo.Code.Once.LinCore.Core.C_Zero_182)
      (coe MAlonzo.Code.Once.LinCore.PassTr.C_initial_722)
      (coe
         MAlonzo.Code.Once.LinCore.PassTr.C__'8728'__674
         (coe
            MAlonzo.Code.Once.LinCore.Core.du_'8988'_'8989'_532
            (coe
               MAlonzo.Code.Once.LinCore.Core.du_sdom_696
               (coe
                  MAlonzo.Code.Once.LinCore.Core.C_sig_694
                  (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                  (coe MAlonzo.Code.Once.Spec.Type.C_Void_20)
                  (coe du_unlinked'45'i_1106))))
         (coe
            MAlonzo.Code.Once.LinCore.PassTr.C_SigOp_794
            (coe
               MAlonzo.Code.Once.LinCore.Core.C_sig_694
               (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
               (coe MAlonzo.Code.Once.Spec.Type.C_Void_20)
               (coe du_unlinked'45'i_1106)))
         (coe MAlonzo.Code.Once.LinCore.PassTr.C_terminal_718))
-- Once.LinCore.FromIR.callAt
d_callAt_1122 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Maybe T_Hit_1076 -> Maybe MAlonzo.Code.Once.LinCore.PassTr.T_IR_650
d_callAt_1122 ~v0 ~v1 ~v2 ~v3 v4 = du_callAt_1122 v4
du_callAt_1122 ::
  Maybe T_Hit_1076 -> Maybe MAlonzo.Code.Once.LinCore.PassTr.T_IR_650
du_callAt_1122 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             C_hit_1096 v2 v3 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe MAlonzo.Code.Once.LinCore.PassTr.C_Call_804 v2 v3 v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe du_unlinked_1114)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR._.trI
d_trI_1140 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1076) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.LinCore.PassTr.T_IR_650
d_trI_1140 v0 ~v1 v2 v3 v4 v5 = du_trI_1140 v0 v2 v3 v4 v5
du_trI_1140 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1076) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.LinCore.PassTr.T_IR_650
du_trI_1140 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_id_666)
      MAlonzo.Code.Once.IR.C__'8728'__28 v6 v8 v9
        -> coe
             MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
             (coe du_trI_1140 (coe v0) (coe v1) (coe v6) (coe v3) (coe v8))
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                     (coe du_trI_1140 (coe v0) (coe v1) (coe v2) (coe v6) (coe v9))
                     (coe
                        (\ v11 ->
                           coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe
                                MAlonzo.Code.Once.LinCore.PassTr.C__'8728'__674
                                (d_'10218'_'10219'_874 (coe v0) (coe v6)) v10 v11)))))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v8 v9
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe du_trI_1140 (coe v0) (coe v1) (coe v2) (coe v10) (coe v8))
                    (coe
                       (\ v12 ->
                          coe
                            MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                            (coe du_trI_1140 (coe v0) (coe v1) (coe v2) (coe v11) (coe v9))
                            (coe
                               (\ v13 ->
                                  coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe
                                       MAlonzo.Code.Once.LinCore.PassTr.C_'10216'_'44'_'10217'_682
                                       v12 v13)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_fst_688)
      MAlonzo.Code.Once.IR.C_snd_48
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_snd_694)
      MAlonzo.Code.Once.IR.C_inl_54
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_inl_700)
      MAlonzo.Code.Once.IR.C_inr_60
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_inr_706)
      MAlonzo.Code.Once.IR.C_case_68 v8 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v10 v11
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe du_trI_1140 (coe v0) (coe v1) (coe v10) (coe v3) (coe v8))
                    (coe
                       (\ v12 ->
                          coe
                            MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                            (coe du_trI_1140 (coe v0) (coe v1) (coe v11) (coe v3) (coe v9))
                            (coe
                               (\ v13 ->
                                  coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe MAlonzo.Code.Once.LinCore.PassTr.C_case_714 v12 v13)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_terminal_718)
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_initial_722)
      MAlonzo.Code.Once.IR.C_curry_86 v9
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24 v10 v11 v12
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe
                       du_trI_1140 (coe v0) (coe v1)
                       (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v2) (coe v10))
                       (coe v12) (coe v9))
                    (coe
                       (\ v13 ->
                          coe
                            MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                            (coe
                               du_gd'63'_1064
                               (coe
                                  d_'10218'_'10219'_874 (coe v0)
                                  (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v2) (coe v10)))
                               (coe d_'10218'_'10219'_874 (coe v0) (coe v12))
                               (coe du_grade_872 (coe v11)) (coe v13))
                            (coe
                               (\ v14 ->
                                  coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe MAlonzo.Code.Once.LinCore.PassTr.C_curry_734 v13 v14)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_94
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_apply_742)
      MAlonzo.Code.Once.IR.C_In_98 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_In_746)
      MAlonzo.Code.Once.IR.C_out'45'μ_102 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_out'45'μ_750)
      MAlonzo.Code.Once.IR.C_Cata_110 v6 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> case coe v11 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v12
                      -> coe
                           MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                           (coe
                              du_trI_1140 (coe v0) (coe v1)
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
                                   (coe MAlonzo.Code.Once.LinCore.PassTr.C_Cata_758 v13)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_114 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_Out_772)
      MAlonzo.Code.Once.IR.C_in'45'ν_118 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_in'45'ν_776)
      MAlonzo.Code.Once.IR.C_Ana_126 v6 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> case coe v3 of
                    MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v12
                      -> coe
                           MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                           (coe
                              du_trI_1140 (coe v0) (coe v1) (coe v2)
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90 (coe v12) (coe v11))
                              (coe v9))
                           (coe
                              (\ v13 ->
                                 coe
                                   MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                                   (coe
                                      du_blk'63'_990
                                      (coe
                                         MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                                         (coe d_'10218'_'10219'_874 (coe v0) (coe v10))
                                         (coe d_'10218'_'10219'_874 (coe v0) (coe v11)))
                                      (coe
                                         MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198
                                         (coe d_lf_876 (coe v0) (coe v12))
                                         (coe d_'10218'_'10219'_874 (coe v0) (coe v11)))
                                      (coe v13))
                                   (coe
                                      (\ v14 ->
                                         coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe
                                              MAlonzo.Code.Once.LinCore.PassTr.C_Ana_768 v13
                                              v14)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Iter_134 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe
                       du_trI_1140 (coe v0) (coe v1) (coe v2)
                       (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v3) (coe v10))
                       (coe v8))
                    (coe
                       (\ v11 ->
                          coe
                            MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                            (coe
                               du_blk'63'_990 (coe d_'10218'_'10219'_874 (coe v0) (coe v2))
                               (coe
                                  d_'10218'_'10219'_874 (coe v0)
                                  (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v3) (coe v10)))
                               (coe v11))
                            (coe
                               (\ v12 ->
                                  coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe MAlonzo.Code.Once.LinCore.PassTr.C_Iter_786 v11 v12)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_138 v6 v7
        -> coe
             seq (coe v6)
             (coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Once.LinCore.PassTr.C_const_790 v7))
      MAlonzo.Code.Once.IR.C_SigOp_144 v5 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Once.LinCore.PassTr.C_SigOp_794
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_sig_694 (coe v5) (coe v6)
                   (coe v7)))
      MAlonzo.Code.Once.IR.C_Call_150 v7
        -> coe du_callAt_1122 (coe v1 v7 v2 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.TrProg
d_TrProg_1254 a0 = ()
data T_TrProg_1254
  = C_trProg_1268 MAlonzo.Code.Once.LinCore.Core.T_Cx_728
                  MAlonzo.Code.Once.LinCore.PassTr.T_Prog_1224
                  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
                   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
                   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1076)
-- Once.LinCore.FromIR.TrProg.Γ
d_Γ_1262 ::
  T_TrProg_1254 -> MAlonzo.Code.Once.LinCore.Core.T_Cx_728
d_Γ_1262 v0
  = case coe v0 of
      C_trProg_1268 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.TrProg.prog
d_prog_1264 ::
  T_TrProg_1254 -> MAlonzo.Code.Once.LinCore.PassTr.T_Prog_1224
d_prog_1264 v0
  = case coe v0 of
      C_trProg_1268 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.TrProg.rs
d_rs_1266 ::
  T_TrProg_1254 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1076
d_rs_1266 v0
  = case coe v0 of
      C_trProg_1268 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.weaken
d_weaken_1278 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_Hit_1076 -> T_Hit_1076
d_weaken_1278 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_weaken_1278 v5
du_weaken_1278 :: T_Hit_1076 -> T_Hit_1076
du_weaken_1278 v0
  = case coe v0 of
      C_hit_1096 v1 v2 v3
        -> coe
             C_hit_1096 (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.LinCore.Core.C_there_754 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.extend-at
d_extend'45'at_1298 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1076) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_Hit_1076
d_extend'45'at_1298 ~v0 v1 v2 v3 ~v4 v5 v6 v7 v8 v9 v10
  = du_extend'45'at_1298 v1 v2 v3 v5 v6 v7 v8 v9 v10
du_extend'45'at_1298 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1076) ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_Hit_1076
du_extend'45'at_1298 v0 v1 v2 v3 v4 v5 v6 v7 v8
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
                                                            C_hit_1096
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
                                                         (coe du_weaken_1278) (coe v2 v3 v4 v5))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              else coe
                                     seq (coe v12)
                                     (coe
                                        MAlonzo.Code.Data.Maybe.Base.du_map_64 (coe du_weaken_1278)
                                        (coe v2 v3 v4 v5))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v10)
                    (coe
                       MAlonzo.Code.Data.Maybe.Base.du_map_64 (coe du_weaken_1278)
                       (coe v2 v3 v4 v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.extend
d_extend_1364 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1076) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1076
d_extend_1364 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_extend_1364 v1 v2 v3 v4 v5 v6 v7
du_extend_1364 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1076) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1076
du_extend_1364 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_extend'45'at_1298 (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
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
d_entry'45'at_1384 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_Prog_1224 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1076) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_650 ->
  Maybe MAlonzo.Code.Once.LinCore.PassTr.T_BlkIR_656 -> T_TrProg_1254
d_entry'45'at_1384 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> coe
             C_trProg_1268
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'9656'__732 (coe v1)
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_sg_726
                   (coe MAlonzo.Code.Once.LinCore.Core.C_once_152)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_act_158)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                   (coe
                      d_'10218'_'10219'_874 (coe v0)
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v4)))
                   (coe
                      d_'10218'_'10219'_874 (coe v0)
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v4)))))
             (coe
                MAlonzo.Code.Once.LinCore.PassTr.C__'9657'_'8739'__1238 v2 v5 v7)
             (coe
                du_extend_1364 (coe v1)
                (coe MAlonzo.Code.Once.LinCore.Core.C_act_158) (coe v3) (coe v4))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             C_trProg_1268
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'9656'__732 (coe v1)
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_sg_726
                   (coe MAlonzo.Code.Once.LinCore.Core.C_once_152)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_eff_160)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                   (coe
                      d_'10218'_'10219'_874 (coe v0)
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v4)))
                   (coe
                      d_'10218'_'10219'_874 (coe v0)
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v4)))))
             (coe
                MAlonzo.Code.Once.LinCore.PassTr.C__'9657'_'8739'__1238 v2 v5
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             (coe
                du_extend_1364 (coe v1)
                (coe MAlonzo.Code.Once.LinCore.Core.C_eff_160) (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.entry
d_entry_1408 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_Prog_1224 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1076) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_650 -> T_TrProg_1254
d_entry_1408 v0 v1 v2 v3 v4 v5
  = coe
      d_entry'45'at_1384 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5)
      (coe
         du_blk'63'_990
         (coe
            d_'10218'_'10219'_874 (coe v0)
            (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v4)))
         (coe
            d_'10218'_'10219'_874 (coe v0)
            (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v4)))
         (coe v5))
-- Once.LinCore.FromIR.trTable
d_trTable_1418 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Maybe T_TrProg_1254
d_trTable_1418 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_trProg_1268 (coe MAlonzo.Code.Once.LinCore.Core.C_ε_730)
                (coe MAlonzo.Code.Once.LinCore.PassTr.C_ε_1226)
                (coe
                   (\ v2 v3 v4 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
             (coe d_trTable_1418 (coe v0) (coe v3))
             (coe
                (\ v4 ->
                   coe
                     MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                     (coe
                        du_trI_1140 (coe v0) (coe d_rs_1266 (coe v4))
                        (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                        (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                        (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2)))
                     (coe
                        (\ v5 ->
                           coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe
                                d_entry_1408 (coe v0) (coe d_Γ_1262 (coe v4))
                                (coe d_prog_1264 (coe v4)) (coe d_rs_1266 (coe v4)) (coe v2)
                                (coe v5))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR._.Tr
d_Tr_1446 a0 a1 a2 a3 a4 a5 a6 = ()
data T_Tr_1446
  = C_t'45'id_1450 | C_t'45''8728'_1466 T_Tr_1446 T_Tr_1446 |
    C_t'45'pair_1482 T_Tr_1446 T_Tr_1446 | C_t'45'fst_1488 |
    C_t'45'snd_1494 | C_t'45'inl_1500 | C_t'45'inr_1506 |
    C_t'45'case_1522 T_Tr_1446 T_Tr_1446 | C_t'45'term_1526 |
    C_t'45'init_1530 | C_t'45'curry_1546 T_Tr_1446 |
    C_t'45'apply_1554 | C_t'45'In_1562 | C_t'45'out_1570 |
    C_t'45'cata_1586 MAlonzo.Code.Once.LinCore.PassTr.T_IR_650
                     T_Tr_1446 |
    C_t'45'Out_1594 | C_t'45'inν_1602 |
    C_t'45'ana_1620 MAlonzo.Code.Once.LinCore.PassTr.T_IR_650
                    T_Tr_1446 |
    C_t'45'iter_1634 T_Tr_1446 | C_t'45'int_1638 | C_t'45'float_1642 |
    C_t'45'op_1650 | C_t'45'hit_1664 | C_t'45'miss_1672
-- Once.LinCore.FromIR._.bind-just
d_bind'45'just_1686 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1076) ->
  () ->
  () ->
  Maybe AgdaAny ->
  (AgdaAny -> Maybe AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bind'45'just_1686 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8
  = du_bind'45'just_1686 v5 v8
du_bind'45'just_1686 ::
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bind'45'just_1686 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR._.trI-Tr
d_trI'45'Tr_1700 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1076) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_650 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_Tr_1446
d_trI'45'Tr_1700 v0 ~v1 v2 v3 v4 v5 ~v6 ~v7
  = du_trI'45'Tr_1700 v0 v2 v3 v4 v5
du_trI'45'Tr_1700 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1076) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_Tr_1446
du_trI'45'Tr_1700 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_t'45'id_1450
      MAlonzo.Code.Once.IR.C__'8728'__28 v6 v8 v9
        -> coe
             C_t'45''8728'_1466
             (coe
                du_trI'45'Tr_1700 (coe v0) (coe v1) (coe v6) (coe v3) (coe v8))
             (coe
                du_trI'45'Tr_1700 (coe v0) (coe v1) (coe v2) (coe v6) (coe v9))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v8 v9
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> coe
                    C_t'45'pair_1482
                    (coe
                       du_trI'45'Tr_1700 (coe v0) (coe v1) (coe v2) (coe v10) (coe v8))
                    (coe
                       du_trI'45'Tr_1700 (coe v0) (coe v1) (coe v2) (coe v11) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_t'45'fst_1488
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_t'45'snd_1494
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_t'45'inl_1500
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_t'45'inr_1506
      MAlonzo.Code.Once.IR.C_case_68 v8 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v10 v11
               -> coe
                    C_t'45'case_1522
                    (coe
                       du_trI'45'Tr_1700 (coe v0) (coe v1) (coe v10) (coe v3) (coe v8))
                    (coe
                       du_trI'45'Tr_1700 (coe v0) (coe v1) (coe v11) (coe v3) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_t'45'term_1526
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_t'45'init_1530
      MAlonzo.Code.Once.IR.C_curry_86 v9
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24 v10 v11 v12
               -> coe
                    C_t'45'curry_1546
                    (coe
                       du_trI'45'Tr_1700 (coe v0) (coe v1)
                       (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v2) (coe v10))
                       (coe v12) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_94 -> coe C_t'45'apply_1554
      MAlonzo.Code.Once.IR.C_In_98 v6 -> coe C_t'45'In_1562
      MAlonzo.Code.Once.IR.C_out'45'μ_102 v6 -> coe C_t'45'out_1570
      MAlonzo.Code.Once.IR.C_Cata_110 v6 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> case coe v11 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v12
                      -> coe
                           C_t'45'cata_1586
                           (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 du_bind'45'just_1686
                                 (coe
                                    du_trI_1140 (coe v0) (coe v1)
                                    (coe
                                       MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v10)
                                       (coe
                                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90 (coe v12)
                                          (coe v3)))
                                    (coe v3) (coe v9))
                                 erased))
                           (coe
                              du_trI'45'Tr_1700 (coe v0) (coe v1)
                              (coe
                                 MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v10)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90 (coe v12)
                                    (coe v3)))
                              (coe v3) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_114 v6 -> coe C_t'45'Out_1594
      MAlonzo.Code.Once.IR.C_in'45'ν_118 v6 -> coe C_t'45'inν_1602
      MAlonzo.Code.Once.IR.C_Ana_126 v6 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> case coe v3 of
                    MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v12
                      -> coe
                           C_t'45'ana_1620
                           (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 du_bind'45'just_1686
                                 (coe
                                    du_trI_1140 (coe v0) (coe v1) (coe v2)
                                    (coe
                                       MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90 (coe v12)
                                       (coe v11))
                                    (coe v9))
                                 erased))
                           (coe
                              du_trI'45'Tr_1700 (coe v0) (coe v1) (coe v2)
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90 (coe v12) (coe v11))
                              (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Iter_134 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
               -> coe
                    C_t'45'iter_1634
                    (coe
                       du_trI'45'Tr_1700 (coe v0) (coe v1) (coe v2)
                       (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v3) (coe v10))
                       (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_138 v6 v7
        -> case coe v6 of
             MAlonzo.Code.Once.IRTy.C_fits'45'int_516 -> coe C_t'45'int_1638
             MAlonzo.Code.Once.IRTy.C_fits'45'float_518 -> coe C_t'45'float_1642
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_SigOp_144 v5 v6 v7 -> coe C_t'45'op_1650
      MAlonzo.Code.Once.IR.C_Call_150 v7
        -> coe du_call'45'tr_1856 (coe v1 v7 v2 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR._._.call-tr
d_call'45'tr_1856 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1076) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_650 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe T_Hit_1076 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_650 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_Tr_1446
d_call'45'tr_1856 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
  = du_call'45'tr_1856 v8
du_call'45'tr_1856 :: Maybe T_Hit_1076 -> T_Tr_1446
du_call'45'tr_1856 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe seq (coe v1) (coe C_t'45'hit_1664)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe C_t'45'miss_1672
      _ -> MAlonzo.RTE.mazUnreachableError
