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
-- Once.LinCore.FromIR._.Sg.cod
d_cod_536 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_cod_536 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_cod_724 (coe v0)
-- Once.LinCore.FromIR._.Sg.dom
d_dom_538 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_dom_538 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_dom_722 (coe v0)
-- Once.LinCore.FromIR._.Sg.env
d_env_540 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_env_540 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_env_720 (coe v0)
-- Once.LinCore.FromIR._.Sg.gr
d_gr_542 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156
d_gr_542 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_gr_718 (coe v0)
-- Once.LinCore.FromIR._.Sg.kd
d_kd_544 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Kd_150
d_kd_544 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_kd_716 (coe v0)
-- Once.LinCore.FromIR._.Sig.info
d_info_548 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_info_548 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_info_692 (coe v0)
-- Once.LinCore.FromIR._.Sig.sA
d_sA_550 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_sA_550 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_sA_688 (coe v0)
-- Once.LinCore.FromIR._.Sig.sB
d_sB_552 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_sB_552 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_sB_690 (coe v0)
-- Once.LinCore.FromIR.P.BlkIR
d_BlkIR_644 a0 a1 a2 a3 a4 = ()
-- Once.LinCore.FromIR.P.GdIR
d_GdIR_650 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_642 -> ()
d_GdIR_650 = erased
-- Once.LinCore.FromIR.P.IR
d_IR_652 a0 a1 a2 a3 = ()
-- Once.LinCore.FromIR.P.InS
d_InS_656 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_InS_656 ~v0 = du_InS_656
du_InS_656 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
du_InS_656 = coe MAlonzo.Code.Once.LinCore.PassTr.du_InS_1102
-- Once.LinCore.FromIR.P.Prog
d_Prog_662 a0 a1 = ()
-- Once.LinCore.FromIR.P.copyIn
d_copyIn_672 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_copyIn_672 ~v0 v1 v2 ~v3 v4 = du_copyIn_672 v1 v2 v4
du_copyIn_672 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_copyIn_672 v0 v1 v2
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
-- Once.LinCore.FromIR.P.dropl
d_dropl_676 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_dropl_676 ~v0 ~v1 ~v2 v3 = du_dropl_676 v3
du_dropl_676 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_dropl_676 v0
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
d_inco_726 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_inco_726 ~v0 = du_inco_726
du_inco_726 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_inco_726 v0 v1
  = coe MAlonzo.Code.Once.LinCore.PassTr.du_inco_1110 v1
-- Once.LinCore.FromIR.P.k-copyIn
d_k'45'copyIn_734 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'copyIn_734 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_k'45'copyIn_734 v5
du_k'45'copyIn_734 ::
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'copyIn_734 v0
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
-- Once.LinCore.FromIR.P.k-dropl
d_k'45'dropl_736 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'dropl_736 ~v0 ~v1 ~v2 ~v3 = du_k'45'dropl_736
du_k'45'dropl_736 :: MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'dropl_736
  = coe
      MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1156
      (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1190)
      (coe
         MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1172
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1236)
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1142))
-- Once.LinCore.FromIR.P.k-inco
d_k'45'inco_738 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'inco_738 ~v0 = du_k'45'inco_738
du_k'45'inco_738 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'inco_738 v0 v1
  = coe MAlonzo.Code.Once.LinCore.PassTr.du_k'45'inco_1118 v1
-- Once.LinCore.FromIR.P.k-mapL
d_k'45'mapL_740 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'mapL_740 ~v0 = du_k'45'mapL_740
du_k'45'mapL_740 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'mapL_740 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Once.LinCore.PassTr.du_k'45'mapL_1074 v4 v6
-- Once.LinCore.FromIR.P.k-withE
d_k'45'withE_742 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'withE_742 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_k'45'withE_742 v5
du_k'45'withE_742 ::
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'withE_742 v0
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
-- Once.LinCore.FromIR.P.mapL
d_mapL_744 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_mapL_744 ~v0 = du_mapL_744
du_mapL_744 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_mapL_744 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.LinCore.PassTr.du_mapL_1034 v3 v4 v5
-- Once.LinCore.FromIR.P.tr
d_tr_752 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_642 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_tr_752 ~v0 = du_tr_752
du_tr_752 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_642 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_tr_752 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.LinCore.PassTr.du_tr_1128 v1 v2 v3
-- Once.LinCore.FromIR.P.tr-blk
d_tr'45'blk_754 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_642 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_BlkIR_648 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_tr'45'blk_754 ~v0 = du_tr'45'blk_754
du_tr'45'blk_754 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_642 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_BlkIR_648 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_tr'45'blk_754 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.LinCore.PassTr.du_tr'45'blk_1138 v1 v2 v3 v4
-- Once.LinCore.FromIR.P.tr-def
d_tr'45'def_756 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_642 -> AgdaAny -> AgdaAny
d_tr'45'def_756 ~v0 = du_tr'45'def_756
du_tr'45'def_756 ::
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_642 -> AgdaAny -> AgdaAny
du_tr'45'def_756 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.LinCore.PassTr.du_tr'45'def_1242 v0 v2 v3 v4 v5
-- Once.LinCore.FromIR.P.tr-gd
d_tr'45'gd_758 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_642 -> AgdaAny -> AgdaAny
d_tr'45'gd_758 ~v0 = du_tr'45'gd_758
du_tr'45'gd_758 ::
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_642 -> AgdaAny -> AgdaAny
du_tr'45'gd_758 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.LinCore.PassTr.du_tr'45'gd_1152 v0 v2 v3 v4 v5 v6
-- Once.LinCore.FromIR.P.trP
d_trP_760 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_Prog_1216 ->
  MAlonzo.Code.Once.LinCore.Core.T_Defs_1812
d_trP_760 ~v0 = du_trP_760
du_trP_760 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_Prog_1216 ->
  MAlonzo.Code.Once.LinCore.Core.T_Defs_1812
du_trP_760 = coe MAlonzo.Code.Once.LinCore.PassTr.du_trP_1248
-- Once.LinCore.FromIR.P.withE
d_withE_762 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_withE_762 ~v0 v1 v2 ~v3 v4 = du_withE_762 v1 v2 v4
du_withE_762 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_withE_762 v0 v1 v2
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
-- Once.LinCore.FromIR.grade
d_grade_864 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156
d_grade_864 ~v0 v1 = du_grade_864 v1
du_grade_864 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156
du_grade_864 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v1
        -> coe MAlonzo.Code.Once.LinCore.Core.C_act_158
      MAlonzo.Code.Once.Spec.Grade.C_eff_44
        -> coe MAlonzo.Code.Once.LinCore.Core.C_eff_160
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.⟪_⟫
d_'10218'_'10219'_866 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_'10218'_'10219'_866 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe MAlonzo.Code.Once.LinCore.Core.C_One_180
      MAlonzo.Code.Once.IRTy.C_Void_18
        -> coe MAlonzo.Code.Once.LinCore.Core.C_Zero_182
      MAlonzo.Code.Once.IRTy.C__'42'__20 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
             (coe d_'10218'_'10219'_866 (coe v0) (coe v2))
             (coe d_'10218'_'10219'_866 (coe v0) (coe v3))
      MAlonzo.Code.Once.IRTy.C__'43'__22 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8853't__186
             (coe d_'10218'_'10219'_866 (coe v0) (coe v2))
             (coe d_'10218'_'10219'_866 (coe v0) (coe v3))
      MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_Fn_190
             (coe MAlonzo.Code.Once.LinCore.Core.C_many_154)
             (coe du_grade_864 (coe v3))
             (coe d_'10218'_'10219'_866 (coe v0) (coe v2))
             (coe d_'10218'_'10219'_866 (coe v0) (coe v4))
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v2
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_μt_194
             (coe d_lf_868 (coe v0) (coe v2))
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v2
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_Nu_192
             (coe d_lf_868 (coe v0) (coe v2))
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
d_lf_868 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134
d_lf_868 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_K_8 v2 -> coe d_lfK_870 (coe v0) (coe v2)
      MAlonzo.Code.Once.IRTy.C_Id_10
        -> coe MAlonzo.Code.Once.LinCore.Core.C_Idf_136
      MAlonzo.Code.Once.IRTy.C__'8853'__12 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8853'f__146
             (coe d_lf_868 (coe v0) (coe v2)) (coe d_lf_868 (coe v0) (coe v3))
      MAlonzo.Code.Once.IRTy.C__'8855'__14 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8855'f__148
             (coe d_lf_868 (coe v0) (coe v2)) (coe d_lf_868 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.lfK
d_lfK_870 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134
d_lfK_870 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe MAlonzo.Code.Once.LinCore.Core.C_Kone_138
      MAlonzo.Code.Once.IRTy.C_Void_18
        -> coe MAlonzo.Code.Once.LinCore.Core.C_Kzero_140
      MAlonzo.Code.Once.IRTy.C__'42'__20 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8855'f__148
             (coe d_lfK_870 (coe v0) (coe v2)) (coe d_lfK_870 (coe v0) (coe v3))
      MAlonzo.Code.Once.IRTy.C__'43'__22 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8853'f__146
             (coe d_lfK_870 (coe v0) (coe v2)) (coe d_lfK_870 (coe v0) (coe v3))
      MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24 v2 v3 v4
        -> coe MAlonzo.Code.Once.LinCore.Core.C_Kzero_140
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v2
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_Kμ_144
             (coe d_lf_868 (coe v0) (coe v2))
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
d_'10218''10219''45'K_914 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IsBaseTypeI_110 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10218''10219''45'K_914 = erased
-- Once.LinCore.FromIR.⟪⟫-TI
d_'10218''10219''45'TI_940 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_132 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10218''10219''45'TI_940 = erased
-- Once.LinCore.FromIR.⟪⌊⌋⟫-flat
d_'10218''8970''8971''10219''45'flat_964 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10218''8970''8971''10219''45'flat_964 = erased
-- Once.LinCore.FromIR.blk?
d_blk'63'_982 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_642 ->
  Maybe MAlonzo.Code.Once.LinCore.PassTr.T_BlkIR_648
d_blk'63'_982 ~v0 ~v1 v2 v3 v4 = du_blk'63'_982 v2 v3 v4
du_blk'63'_982 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_642 ->
  Maybe MAlonzo.Code.Once.LinCore.PassTr.T_BlkIR_648
du_blk'63'_982 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.LinCore.PassTr.C_id_658
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'id_800)
      MAlonzo.Code.Once.LinCore.PassTr.C__'8728'__666 v4 v6 v7
        -> coe
             MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
             (coe du_blk'63'_982 (coe v4) (coe v1) (coe v6))
             (coe
                (\ v8 ->
                   coe
                     MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                     (coe du_blk'63'_982 (coe v0) (coe v4) (coe v7))
                     (coe
                        (\ v9 ->
                           coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45''8728'_812 v8 v9)))))
      MAlonzo.Code.Once.LinCore.PassTr.C_'10216'_'44'_'10217'_674 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v8 v9
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe du_blk'63'_982 (coe v0) (coe v8) (coe v6))
                    (coe
                       (\ v10 ->
                          coe
                            MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                            (coe du_blk'63'_982 (coe v0) (coe v9) (coe v7))
                            (coe
                               (\ v11 ->
                                  coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe
                                       MAlonzo.Code.Once.LinCore.PassTr.C_i'45'pair_824 v10 v11)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.PassTr.C_fst_680
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'fst_830)
      MAlonzo.Code.Once.LinCore.PassTr.C_snd_686
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'snd_836)
      MAlonzo.Code.Once.LinCore.PassTr.C_inl_692
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'inl_842)
      MAlonzo.Code.Once.LinCore.PassTr.C_inr_698
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'inr_848)
      MAlonzo.Code.Once.LinCore.PassTr.C_case_706 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v8 v9
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe du_blk'63'_982 (coe v8) (coe v1) (coe v6))
                    (coe
                       (\ v10 ->
                          coe
                            MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                            (coe du_blk'63'_982 (coe v9) (coe v1) (coe v7))
                            (coe
                               (\ v11 ->
                                  coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe
                                       MAlonzo.Code.Once.LinCore.PassTr.C_i'45'case_860 v10 v11)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.PassTr.C_terminal_710
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'term_864)
      MAlonzo.Code.Once.LinCore.PassTr.C_initial_714
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'init_868)
      MAlonzo.Code.Once.LinCore.PassTr.C_curry_726 v7 v8
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'curry_882)
      MAlonzo.Code.Once.LinCore.PassTr.C_apply_734
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v8 v9 v10 v11
                      -> case coe v9 of
                           MAlonzo.Code.Once.LinCore.Core.C_act_158
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                  (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'apply_888)
                           MAlonzo.Code.Once.LinCore.Core.C_eff_160
                             -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.PassTr.C_In_738
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'In_892)
      MAlonzo.Code.Once.LinCore.PassTr.C_out'45'μ_742
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'out_896)
      MAlonzo.Code.Once.LinCore.PassTr.C_Cata_750 v6
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v7 v8
               -> case coe v8 of
                    MAlonzo.Code.Once.LinCore.Core.C_μt_194 v9
                      -> coe
                           MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                           (coe
                              du_blk'63'_982
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
                                   (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'cata_906 v10)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.PassTr.C_Ana_760 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'ana_918)
      MAlonzo.Code.Once.LinCore.PassTr.C_Out_764
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'Out_922)
      MAlonzo.Code.Once.LinCore.PassTr.C_in'45'ν_768
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'inν_926)
      MAlonzo.Code.Once.LinCore.PassTr.C_Iter_778 v6 v7
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.LinCore.PassTr.C_const_782 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'const_932)
      MAlonzo.Code.Once.LinCore.PassTr.C_SigOp_786 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'op_936)
      MAlonzo.Code.Once.LinCore.PassTr.C_Call_796 v3 v4 v7
        -> case coe v4 of
             MAlonzo.Code.Once.LinCore.Core.C_act_158
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'call_946)
             MAlonzo.Code.Once.LinCore.Core.C_eff_160
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.gd?
d_gd'63'_1056 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_642 -> Maybe AgdaAny
d_gd'63'_1056 ~v0 ~v1 v2 v3 v4 v5 = du_gd'63'_1056 v2 v3 v4 v5
du_gd'63'_1056 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_642 -> Maybe AgdaAny
du_gd'63'_1056 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.LinCore.Core.C_act_158
        -> coe du_blk'63'_982 (coe v0) (coe v1) (coe v3)
      MAlonzo.Code.Once.LinCore.Core.C_eff_160
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.Hit
d_Hit_1068 a0 a1 a2 a3 = ()
data T_Hit_1068
  = C_hit_1088 Integer MAlonzo.Code.Once.LinCore.Core.T_Gr_156
               MAlonzo.Code.Once.LinCore.Core.T__'8715''91'_'93'__738
-- Once.LinCore.FromIR.Hit.l
d_l_1082 :: T_Hit_1068 -> Integer
d_l_1082 v0
  = case coe v0 of
      C_hit_1088 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.Hit.g
d_g_1084 :: T_Hit_1068 -> MAlonzo.Code.Once.LinCore.Core.T_Gr_156
d_g_1084 v0
  = case coe v0 of
      C_hit_1088 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.Hit.p
d_p_1086 ::
  T_Hit_1068 ->
  MAlonzo.Code.Once.LinCore.Core.T__'8715''91'_'93'__738
d_p_1086 v0
  = case coe v0 of
      C_hit_1088 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.Resolver
d_Resolver_1090 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 -> ()
d_Resolver_1090 = erased
-- Once.LinCore.FromIR.unlinked-i
d_unlinked'45'i_1098 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_unlinked'45'i_1098 ~v0 = du_unlinked'45'i_1098
du_unlinked'45'i_1098 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
du_unlinked'45'i_1098
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
d_unlinked_1106 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_642
d_unlinked_1106 ~v0 ~v1 ~v2 ~v3 = du_unlinked_1106
du_unlinked_1106 :: MAlonzo.Code.Once.LinCore.PassTr.T_IR_642
du_unlinked_1106
  = coe
      MAlonzo.Code.Once.LinCore.PassTr.C__'8728'__666
      (coe MAlonzo.Code.Once.LinCore.Core.C_Zero_182)
      (coe MAlonzo.Code.Once.LinCore.PassTr.C_initial_714)
      (coe
         MAlonzo.Code.Once.LinCore.PassTr.C__'8728'__666
         (coe
            MAlonzo.Code.Once.LinCore.Core.du_'8988'_'8989'_532
            (coe
               MAlonzo.Code.Once.LinCore.Core.du_sdom_696
               (coe
                  MAlonzo.Code.Once.LinCore.Core.C_sig_694
                  (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                  (coe MAlonzo.Code.Once.Spec.Type.C_Void_20)
                  (coe du_unlinked'45'i_1098))))
         (coe
            MAlonzo.Code.Once.LinCore.PassTr.C_SigOp_786
            (coe
               MAlonzo.Code.Once.LinCore.Core.C_sig_694
               (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
               (coe MAlonzo.Code.Once.Spec.Type.C_Void_20)
               (coe du_unlinked'45'i_1098)))
         (coe MAlonzo.Code.Once.LinCore.PassTr.C_terminal_710))
-- Once.LinCore.FromIR.callAt
d_callAt_1114 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Maybe T_Hit_1068 -> Maybe MAlonzo.Code.Once.LinCore.PassTr.T_IR_642
d_callAt_1114 ~v0 ~v1 ~v2 ~v3 v4 = du_callAt_1114 v4
du_callAt_1114 ::
  Maybe T_Hit_1068 -> Maybe MAlonzo.Code.Once.LinCore.PassTr.T_IR_642
du_callAt_1114 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> case coe v1 of
             C_hit_1088 v2 v3 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe MAlonzo.Code.Once.LinCore.PassTr.C_Call_796 v2 v3 v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe du_unlinked_1106)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR._.trI
d_trI_1132 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1068) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.LinCore.PassTr.T_IR_642
d_trI_1132 v0 ~v1 v2 v3 v4 v5 = du_trI_1132 v0 v2 v3 v4 v5
du_trI_1132 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1068) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.LinCore.PassTr.T_IR_642
du_trI_1132 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_id_658)
      MAlonzo.Code.Once.IR.C__'8728'__28 v6 v8 v9
        -> coe
             MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
             (coe du_trI_1132 (coe v0) (coe v1) (coe v6) (coe v3) (coe v8))
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                     (coe du_trI_1132 (coe v0) (coe v1) (coe v2) (coe v6) (coe v9))
                     (coe
                        (\ v11 ->
                           coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe
                                MAlonzo.Code.Once.LinCore.PassTr.C__'8728'__666
                                (d_'10218'_'10219'_866 (coe v0) (coe v6)) v10 v11)))))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v8 v9
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe du_trI_1132 (coe v0) (coe v1) (coe v2) (coe v10) (coe v8))
                    (coe
                       (\ v12 ->
                          coe
                            MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                            (coe du_trI_1132 (coe v0) (coe v1) (coe v2) (coe v11) (coe v9))
                            (coe
                               (\ v13 ->
                                  coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe
                                       MAlonzo.Code.Once.LinCore.PassTr.C_'10216'_'44'_'10217'_674
                                       v12 v13)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_fst_680)
      MAlonzo.Code.Once.IR.C_snd_48
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_snd_686)
      MAlonzo.Code.Once.IR.C_inl_54
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_inl_692)
      MAlonzo.Code.Once.IR.C_inr_60
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_inr_698)
      MAlonzo.Code.Once.IR.C_case_68 v8 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v10 v11
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe du_trI_1132 (coe v0) (coe v1) (coe v10) (coe v3) (coe v8))
                    (coe
                       (\ v12 ->
                          coe
                            MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                            (coe du_trI_1132 (coe v0) (coe v1) (coe v11) (coe v3) (coe v9))
                            (coe
                               (\ v13 ->
                                  coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe MAlonzo.Code.Once.LinCore.PassTr.C_case_706 v12 v13)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_terminal_710)
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_initial_714)
      MAlonzo.Code.Once.IR.C_curry_86 v9
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24 v10 v11 v12
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe
                       du_trI_1132 (coe v0) (coe v1)
                       (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v2) (coe v10))
                       (coe v12) (coe v9))
                    (coe
                       (\ v13 ->
                          coe
                            MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                            (coe
                               du_gd'63'_1056
                               (coe
                                  d_'10218'_'10219'_866 (coe v0)
                                  (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v2) (coe v10)))
                               (coe d_'10218'_'10219'_866 (coe v0) (coe v12))
                               (coe du_grade_864 (coe v11)) (coe v13))
                            (coe
                               (\ v14 ->
                                  coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe MAlonzo.Code.Once.LinCore.PassTr.C_curry_726 v13 v14)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_94
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_apply_734)
      MAlonzo.Code.Once.IR.C_In_98 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_In_738)
      MAlonzo.Code.Once.IR.C_out'45'μ_102 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_out'45'μ_742)
      MAlonzo.Code.Once.IR.C_Cata_110 v6 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> case coe v11 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v12
                      -> coe
                           MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                           (coe
                              du_trI_1132 (coe v0) (coe v1)
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
                                   (coe MAlonzo.Code.Once.LinCore.PassTr.C_Cata_750 v13)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_114 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_Out_764)
      MAlonzo.Code.Once.IR.C_in'45'ν_118 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_in'45'ν_768)
      MAlonzo.Code.Once.IR.C_Ana_126 v6 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> case coe v3 of
                    MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v12
                      -> coe
                           MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                           (coe
                              du_trI_1132 (coe v0) (coe v1) (coe v2)
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90 (coe v12) (coe v11))
                              (coe v9))
                           (coe
                              (\ v13 ->
                                 coe
                                   MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                                   (coe
                                      du_blk'63'_982
                                      (coe
                                         MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                                         (coe d_'10218'_'10219'_866 (coe v0) (coe v10))
                                         (coe d_'10218'_'10219'_866 (coe v0) (coe v11)))
                                      (coe
                                         MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198
                                         (coe d_lf_868 (coe v0) (coe v12))
                                         (coe d_'10218'_'10219'_866 (coe v0) (coe v11)))
                                      (coe v13))
                                   (coe
                                      (\ v14 ->
                                         coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe
                                              MAlonzo.Code.Once.LinCore.PassTr.C_Ana_760 v13
                                              v14)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Iter_134 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe
                       du_trI_1132 (coe v0) (coe v1) (coe v2)
                       (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v3) (coe v10))
                       (coe v8))
                    (coe
                       (\ v11 ->
                          coe
                            MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                            (coe
                               du_blk'63'_982 (coe d_'10218'_'10219'_866 (coe v0) (coe v2))
                               (coe
                                  d_'10218'_'10219'_866 (coe v0)
                                  (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v3) (coe v10)))
                               (coe v11))
                            (coe
                               (\ v12 ->
                                  coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe MAlonzo.Code.Once.LinCore.PassTr.C_Iter_778 v11 v12)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_138 v6 v7
        -> coe
             seq (coe v6)
             (coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Once.LinCore.PassTr.C_const_782 v7))
      MAlonzo.Code.Once.IR.C_SigOp_144 v5 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Once.LinCore.PassTr.C_SigOp_786
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_sig_694 (coe v5) (coe v6)
                   (coe v7)))
      MAlonzo.Code.Once.IR.C_Call_150 v7
        -> coe du_callAt_1114 (coe v1 v7 v2 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.TrProg
d_TrProg_1246 a0 = ()
data T_TrProg_1246
  = C_trProg_1260 MAlonzo.Code.Once.LinCore.Core.T_Cx_728
                  MAlonzo.Code.Once.LinCore.PassTr.T_Prog_1216
                  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
                   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
                   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1068)
-- Once.LinCore.FromIR.TrProg.Γ
d_Γ_1254 ::
  T_TrProg_1246 -> MAlonzo.Code.Once.LinCore.Core.T_Cx_728
d_Γ_1254 v0
  = case coe v0 of
      C_trProg_1260 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.TrProg.prog
d_prog_1256 ::
  T_TrProg_1246 -> MAlonzo.Code.Once.LinCore.PassTr.T_Prog_1216
d_prog_1256 v0
  = case coe v0 of
      C_trProg_1260 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.TrProg.rs
d_rs_1258 ::
  T_TrProg_1246 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1068
d_rs_1258 v0
  = case coe v0 of
      C_trProg_1260 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.weaken
d_weaken_1270 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_Hit_1068 -> T_Hit_1068
d_weaken_1270 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_weaken_1270 v5
du_weaken_1270 :: T_Hit_1068 -> T_Hit_1068
du_weaken_1270 v0
  = case coe v0 of
      C_hit_1088 v1 v2 v3
        -> coe
             C_hit_1088 (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.LinCore.Core.C_there_754 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.extend-at
d_extend'45'at_1290 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1068) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_Hit_1068
d_extend'45'at_1290 ~v0 v1 v2 v3 ~v4 v5 v6 v7 v8 v9 v10
  = du_extend'45'at_1290 v1 v2 v3 v5 v6 v7 v8 v9 v10
du_extend'45'at_1290 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1068) ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_Hit_1068
du_extend'45'at_1290 v0 v1 v2 v3 v4 v5 v6 v7 v8
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
                                                            C_hit_1088
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
                                                         (coe du_weaken_1270) (coe v2 v3 v4 v5))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              else coe
                                     seq (coe v12)
                                     (coe
                                        MAlonzo.Code.Data.Maybe.Base.du_map_64 (coe du_weaken_1270)
                                        (coe v2 v3 v4 v5))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v10)
                    (coe
                       MAlonzo.Code.Data.Maybe.Base.du_map_64 (coe du_weaken_1270)
                       (coe v2 v3 v4 v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.extend
d_extend_1356 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1068) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1068
d_extend_1356 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_extend_1356 v1 v2 v3 v4 v5 v6 v7
du_extend_1356 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1068) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1068
du_extend_1356 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_extend'45'at_1290 (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
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
d_entry'45'at_1376 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_Prog_1216 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1068) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_642 ->
  Maybe MAlonzo.Code.Once.LinCore.PassTr.T_BlkIR_648 -> T_TrProg_1246
d_entry'45'at_1376 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> coe
             C_trProg_1260
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'9656'__732 (coe v1)
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_sg_726
                   (coe MAlonzo.Code.Once.LinCore.Core.C_once_152)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_act_158)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                   (coe
                      d_'10218'_'10219'_866 (coe v0)
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v4)))
                   (coe
                      d_'10218'_'10219'_866 (coe v0)
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v4)))))
             (coe
                MAlonzo.Code.Once.LinCore.PassTr.C__'9657'_'8739'__1230 v2 v5 v7)
             (coe
                du_extend_1356 (coe v1)
                (coe MAlonzo.Code.Once.LinCore.Core.C_act_158) (coe v3) (coe v4))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             C_trProg_1260
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'9656'__732 (coe v1)
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_sg_726
                   (coe MAlonzo.Code.Once.LinCore.Core.C_once_152)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_eff_160)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                   (coe
                      d_'10218'_'10219'_866 (coe v0)
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v4)))
                   (coe
                      d_'10218'_'10219'_866 (coe v0)
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v4)))))
             (coe
                MAlonzo.Code.Once.LinCore.PassTr.C__'9657'_'8739'__1230 v2 v5
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             (coe
                du_extend_1356 (coe v1)
                (coe MAlonzo.Code.Once.LinCore.Core.C_eff_160) (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.entry
d_entry_1400 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_Prog_1216 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1068) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_642 -> T_TrProg_1246
d_entry_1400 v0 v1 v2 v3 v4 v5
  = coe
      d_entry'45'at_1376 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5)
      (coe
         du_blk'63'_982
         (coe
            d_'10218'_'10219'_866 (coe v0)
            (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v4)))
         (coe
            d_'10218'_'10219'_866 (coe v0)
            (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v4)))
         (coe v5))
-- Once.LinCore.FromIR.trTable
d_trTable_1410 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Maybe T_TrProg_1246
d_trTable_1410 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_trProg_1260 (coe MAlonzo.Code.Once.LinCore.Core.C_ε_730)
                (coe MAlonzo.Code.Once.LinCore.PassTr.C_ε_1218)
                (coe
                   (\ v2 v3 v4 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
             (coe d_trTable_1410 (coe v0) (coe v3))
             (coe
                (\ v4 ->
                   coe
                     MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                     (coe
                        du_trI_1132 (coe v0) (coe d_rs_1258 (coe v4))
                        (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                        (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                        (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2)))
                     (coe
                        (\ v5 ->
                           coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe
                                d_entry_1400 (coe v0) (coe d_Γ_1254 (coe v4))
                                (coe d_prog_1256 (coe v4)) (coe d_rs_1258 (coe v4)) (coe v2)
                                (coe v5))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR._.Tr
d_Tr_1438 a0 a1 a2 a3 a4 a5 a6 = ()
data T_Tr_1438
  = C_t'45'id_1442 | C_t'45''8728'_1458 T_Tr_1438 T_Tr_1438 |
    C_t'45'pair_1474 T_Tr_1438 T_Tr_1438 | C_t'45'fst_1480 |
    C_t'45'snd_1486 | C_t'45'inl_1492 | C_t'45'inr_1498 |
    C_t'45'case_1514 T_Tr_1438 T_Tr_1438 | C_t'45'term_1518 |
    C_t'45'init_1522 | C_t'45'curry_1538 T_Tr_1438 |
    C_t'45'apply_1546 | C_t'45'In_1554 | C_t'45'out_1562 |
    C_t'45'cata_1578 MAlonzo.Code.Once.LinCore.PassTr.T_IR_642
                     T_Tr_1438 |
    C_t'45'Out_1586 | C_t'45'inν_1594 |
    C_t'45'ana_1612 MAlonzo.Code.Once.LinCore.PassTr.T_IR_642
                    T_Tr_1438 |
    C_t'45'iter_1626 T_Tr_1438 | C_t'45'int_1630 | C_t'45'float_1634 |
    C_t'45'op_1642 | C_t'45'hit_1656 | C_t'45'miss_1664
-- Once.LinCore.FromIR._.bind-just
d_bind'45'just_1678 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1068) ->
  () ->
  () ->
  Maybe AgdaAny ->
  (AgdaAny -> Maybe AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bind'45'just_1678 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8
  = du_bind'45'just_1678 v5 v8
du_bind'45'just_1678 ::
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bind'45'just_1678 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR._.trI-Tr
d_trI'45'Tr_1692 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1068) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_642 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_Tr_1438
d_trI'45'Tr_1692 v0 ~v1 v2 v3 v4 v5 ~v6 ~v7
  = du_trI'45'Tr_1692 v0 v2 v3 v4 v5
du_trI'45'Tr_1692 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1068) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_Tr_1438
du_trI'45'Tr_1692 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_t'45'id_1442
      MAlonzo.Code.Once.IR.C__'8728'__28 v6 v8 v9
        -> coe
             C_t'45''8728'_1458
             (coe
                du_trI'45'Tr_1692 (coe v0) (coe v1) (coe v6) (coe v3) (coe v8))
             (coe
                du_trI'45'Tr_1692 (coe v0) (coe v1) (coe v2) (coe v6) (coe v9))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v8 v9
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> coe
                    C_t'45'pair_1474
                    (coe
                       du_trI'45'Tr_1692 (coe v0) (coe v1) (coe v2) (coe v10) (coe v8))
                    (coe
                       du_trI'45'Tr_1692 (coe v0) (coe v1) (coe v2) (coe v11) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_t'45'fst_1480
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_t'45'snd_1486
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_t'45'inl_1492
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_t'45'inr_1498
      MAlonzo.Code.Once.IR.C_case_68 v8 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v10 v11
               -> coe
                    C_t'45'case_1514
                    (coe
                       du_trI'45'Tr_1692 (coe v0) (coe v1) (coe v10) (coe v3) (coe v8))
                    (coe
                       du_trI'45'Tr_1692 (coe v0) (coe v1) (coe v11) (coe v3) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_t'45'term_1518
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_t'45'init_1522
      MAlonzo.Code.Once.IR.C_curry_86 v9
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24 v10 v11 v12
               -> coe
                    C_t'45'curry_1538
                    (coe
                       du_trI'45'Tr_1692 (coe v0) (coe v1)
                       (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v2) (coe v10))
                       (coe v12) (coe v9))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_94 -> coe C_t'45'apply_1546
      MAlonzo.Code.Once.IR.C_In_98 v6 -> coe C_t'45'In_1554
      MAlonzo.Code.Once.IR.C_out'45'μ_102 v6 -> coe C_t'45'out_1562
      MAlonzo.Code.Once.IR.C_Cata_110 v6 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> case coe v11 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v12
                      -> coe
                           C_t'45'cata_1578
                           (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 du_bind'45'just_1678
                                 (coe
                                    du_trI_1132 (coe v0) (coe v1)
                                    (coe
                                       MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v10)
                                       (coe
                                          MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90 (coe v12)
                                          (coe v3)))
                                    (coe v3) (coe v9))
                                 erased))
                           (coe
                              du_trI'45'Tr_1692 (coe v0) (coe v1)
                              (coe
                                 MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v10)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90 (coe v12)
                                    (coe v3)))
                              (coe v3) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_114 v6 -> coe C_t'45'Out_1586
      MAlonzo.Code.Once.IR.C_in'45'ν_118 v6 -> coe C_t'45'inν_1594
      MAlonzo.Code.Once.IR.C_Ana_126 v6 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> case coe v3 of
                    MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v12
                      -> coe
                           C_t'45'ana_1612
                           (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                              (coe
                                 du_bind'45'just_1678
                                 (coe
                                    du_trI_1132 (coe v0) (coe v1) (coe v2)
                                    (coe
                                       MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90 (coe v12)
                                       (coe v11))
                                    (coe v9))
                                 erased))
                           (coe
                              du_trI'45'Tr_1692 (coe v0) (coe v1) (coe v2)
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90 (coe v12) (coe v11))
                              (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Iter_134 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
               -> coe
                    C_t'45'iter_1626
                    (coe
                       du_trI'45'Tr_1692 (coe v0) (coe v1) (coe v2)
                       (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v3) (coe v10))
                       (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_138 v6 v7
        -> case coe v6 of
             MAlonzo.Code.Once.IRTy.C_fits'45'int_516 -> coe C_t'45'int_1630
             MAlonzo.Code.Once.IRTy.C_fits'45'float_518 -> coe C_t'45'float_1634
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_SigOp_144 v5 v6 v7 -> coe C_t'45'op_1642
      MAlonzo.Code.Once.IR.C_Call_150 v7
        -> coe du_call'45'tr_1848 (coe v1 v7 v2 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR._._.call-tr
d_call'45'tr_1848 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1068) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_642 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Maybe T_Hit_1068 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_642 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_Tr_1438
d_call'45'tr_1848 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11
  = du_call'45'tr_1848 v8
du_call'45'tr_1848 :: Maybe T_Hit_1068 -> T_Tr_1438
du_call'45'tr_1848 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe seq (coe v1) (coe C_t'45'hit_1656)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe C_t'45'miss_1664
      _ -> MAlonzo.RTE.mazUnreachableError
