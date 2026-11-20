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
d_flat_144 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
d_flat_144 ~v0 = du_flat_144
du_flat_144 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Once.LinCore.Flat.T_FTy_8
du_flat_144 = coe MAlonzo.Code.Once.LinCore.Core.du_flat_606
-- Once.LinCore.FromIR._.⌜_⌝
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
-- Once.LinCore.FromIR._.Sg.cod
d_cod_514 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_cod_514 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_cod_724 (coe v0)
-- Once.LinCore.FromIR._.Sg.dom
d_dom_516 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_dom_516 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_dom_722 (coe v0)
-- Once.LinCore.FromIR._.Sg.env
d_env_518 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_env_518 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_env_720 (coe v0)
-- Once.LinCore.FromIR._.Sg.gr
d_gr_520 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156
d_gr_520 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_gr_718 (coe v0)
-- Once.LinCore.FromIR._.Sg.kd
d_kd_522 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Kd_150
d_kd_522 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_kd_716 (coe v0)
-- Once.LinCore.FromIR._.Sig.info
d_info_526 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_info_526 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_info_692 (coe v0)
-- Once.LinCore.FromIR._.Sig.sA
d_sA_528 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_sA_528 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_sA_688 (coe v0)
-- Once.LinCore.FromIR._.Sig.sB
d_sB_530 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sig_680 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_sB_530 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_sB_690 (coe v0)
-- Once.LinCore.FromIR.P.BlkIR
d_BlkIR_618 a0 a1 a2 a3 a4 = ()
-- Once.LinCore.FromIR.P.GdIR
d_GdIR_624 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_616 -> ()
d_GdIR_624 = erased
-- Once.LinCore.FromIR.P.IR
d_IR_626 a0 a1 a2 a3 = ()
-- Once.LinCore.FromIR.P.InS
d_InS_630 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_InS_630 ~v0 = du_InS_630
du_InS_630 ::
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
du_InS_630 = coe MAlonzo.Code.Once.LinCore.PassTr.du_InS_1076
-- Once.LinCore.FromIR.P.Prog
d_Prog_636 a0 a1 = ()
-- Once.LinCore.FromIR.P.copyIn
d_copyIn_646 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_copyIn_646 ~v0 v1 v2 ~v3 v4 = du_copyIn_646 v1 v2 v4
du_copyIn_646 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_copyIn_646 v0 v1 v2
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
d_dropl_650 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_dropl_650 ~v0 ~v1 ~v2 v3 = du_dropl_650 v3
du_dropl_650 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_dropl_650 v0
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
d_inco_700 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_inco_700 ~v0 = du_inco_700
du_inco_700 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_inco_700 v0 v1
  = coe MAlonzo.Code.Once.LinCore.PassTr.du_inco_1084 v1
-- Once.LinCore.FromIR.P.k-copyIn
d_k'45'copyIn_708 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'copyIn_708 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_k'45'copyIn_708 v5
du_k'45'copyIn_708 ::
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'copyIn_708 v0
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
-- Once.LinCore.FromIR.P.k-dropl
d_k'45'dropl_710 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'dropl_710 ~v0 ~v1 ~v2 ~v3 = du_k'45'dropl_710
du_k'45'dropl_710 :: MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'dropl_710
  = coe
      MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1132
      (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1166)
      (coe
         MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1148
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1212)
         (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1118))
-- Once.LinCore.FromIR.P.k-inco
d_k'45'inco_712 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'inco_712 ~v0 = du_k'45'inco_712
du_k'45'inco_712 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'inco_712 v0 v1
  = coe MAlonzo.Code.Once.LinCore.PassTr.du_k'45'inco_1092 v1
-- Once.LinCore.FromIR.P.k-mapL
d_k'45'mapL_714 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'mapL_714 ~v0 = du_k'45'mapL_714
du_k'45'mapL_714 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'mapL_714 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Once.LinCore.PassTr.du_k'45'mapL_1048 v4 v6
-- Once.LinCore.FromIR.P.k-withE
d_k'45'withE_716 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'withE_716 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_k'45'withE_716 v5
du_k'45'withE_716 ::
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'withE_716 v0
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
-- Once.LinCore.FromIR.P.mapL
d_mapL_718 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_mapL_718 ~v0 = du_mapL_718
du_mapL_718 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_mapL_718 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Once.LinCore.PassTr.du_mapL_1008 v3 v4 v5
-- Once.LinCore.FromIR.P.tr
d_tr_726 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_616 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_tr_726 ~v0 = du_tr_726
du_tr_726 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_616 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_tr_726 v0 v1 v2 v3
  = coe MAlonzo.Code.Once.LinCore.PassTr.du_tr_1102 v1 v2 v3
-- Once.LinCore.FromIR.P.tr-blk
d_tr'45'blk_728 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_616 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_BlkIR_622 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_tr'45'blk_728 ~v0 = du_tr'45'blk_728
du_tr'45'blk_728 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_616 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_BlkIR_622 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_tr'45'blk_728 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.LinCore.PassTr.du_tr'45'blk_1112 v1 v2 v3 v4
-- Once.LinCore.FromIR.P.tr-def
d_tr'45'def_730 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_616 -> AgdaAny -> AgdaAny
d_tr'45'def_730 ~v0 = du_tr'45'def_730
du_tr'45'def_730 ::
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_616 -> AgdaAny -> AgdaAny
du_tr'45'def_730 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.LinCore.PassTr.du_tr'45'def_1216 v0 v2 v3 v4 v5
-- Once.LinCore.FromIR.P.tr-gd
d_tr'45'gd_732 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_616 -> AgdaAny -> AgdaAny
d_tr'45'gd_732 ~v0 = du_tr'45'gd_732
du_tr'45'gd_732 ::
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_616 -> AgdaAny -> AgdaAny
du_tr'45'gd_732 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Once.LinCore.PassTr.du_tr'45'gd_1126 v0 v2 v3 v4 v5 v6
-- Once.LinCore.FromIR.P.trP
d_trP_734 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_Prog_1190 ->
  MAlonzo.Code.Once.LinCore.Core.T_Defs_1682
d_trP_734 ~v0 = du_trP_734
du_trP_734 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_Prog_1190 ->
  MAlonzo.Code.Once.LinCore.Core.T_Defs_1682
du_trP_734 = coe MAlonzo.Code.Once.LinCore.PassTr.du_trP_1222
-- Once.LinCore.FromIR.P.withE
d_withE_736 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_withE_736 ~v0 v1 v2 ~v3 v4 = du_withE_736 v1 v2 v4
du_withE_736 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_withE_736 v0 v1 v2
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
d_grade_838 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156
d_grade_838 ~v0 v1 = du_grade_838 v1
du_grade_838 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156
du_grade_838 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v1
        -> coe MAlonzo.Code.Once.LinCore.Core.C_act_158
      MAlonzo.Code.Once.Spec.Grade.C_eff_44
        -> coe MAlonzo.Code.Once.LinCore.Core.C_eff_160
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.⟪_⟫
d_'10218'_'10219'_840 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_'10218'_'10219'_840 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe MAlonzo.Code.Once.LinCore.Core.C_One_180
      MAlonzo.Code.Once.IRTy.C_Void_18
        -> coe MAlonzo.Code.Once.LinCore.Core.C_Zero_182
      MAlonzo.Code.Once.IRTy.C__'42'__20 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
             (coe d_'10218'_'10219'_840 (coe v0) (coe v2))
             (coe d_'10218'_'10219'_840 (coe v0) (coe v3))
      MAlonzo.Code.Once.IRTy.C__'43'__22 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8853't__186
             (coe d_'10218'_'10219'_840 (coe v0) (coe v2))
             (coe d_'10218'_'10219'_840 (coe v0) (coe v3))
      MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24 v2 v3 v4
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_Fn_190
             (coe MAlonzo.Code.Once.LinCore.Core.C_many_154)
             (coe du_grade_838 (coe v3))
             (coe d_'10218'_'10219'_840 (coe v0) (coe v2))
             (coe d_'10218'_'10219'_840 (coe v0) (coe v4))
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v2
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_μt_194
             (coe d_lf_842 (coe v0) (coe v2))
      MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v2
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_Nu_192
             (coe d_lf_842 (coe v0) (coe v2))
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
d_lf_842 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134
d_lf_842 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_K_8 v2 -> coe d_lfK_844 (coe v0) (coe v2)
      MAlonzo.Code.Once.IRTy.C_Id_10
        -> coe MAlonzo.Code.Once.LinCore.Core.C_Idf_136
      MAlonzo.Code.Once.IRTy.C__'8853'__12 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8853'f__146
             (coe d_lf_842 (coe v0) (coe v2)) (coe d_lf_842 (coe v0) (coe v3))
      MAlonzo.Code.Once.IRTy.C__'8855'__14 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8855'f__148
             (coe d_lf_842 (coe v0) (coe v2)) (coe d_lf_842 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.lfK
d_lfK_844 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LF_134
d_lfK_844 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.IRTy.C_Unit_16
        -> coe MAlonzo.Code.Once.LinCore.Core.C_Kone_138
      MAlonzo.Code.Once.IRTy.C_Void_18
        -> coe MAlonzo.Code.Once.LinCore.Core.C_Kzero_140
      MAlonzo.Code.Once.IRTy.C__'42'__20 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8855'f__148
             (coe d_lfK_844 (coe v0) (coe v2)) (coe d_lfK_844 (coe v0) (coe v3))
      MAlonzo.Code.Once.IRTy.C__'43'__22 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8853'f__146
             (coe d_lfK_844 (coe v0) (coe v2)) (coe d_lfK_844 (coe v0) (coe v3))
      MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24 v2 v3 v4
        -> coe MAlonzo.Code.Once.LinCore.Core.C_Kzero_140
      MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v2
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_Kμ_144
             (coe d_lf_842 (coe v0) (coe v2))
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
d_'10218''10219''45'K_888 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IsBaseTypeI_110 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10218''10219''45'K_888 = erased
-- Once.LinCore.FromIR.⟪⟫-TI
d_'10218''10219''45'TI_914 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_132 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10218''10219''45'TI_914 = erased
-- Once.LinCore.FromIR.⟪⌊⌋⟫-flat
d_'10218''8970''8971''10219''45'flat_938 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Base_84 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'10218''8970''8971''10219''45'flat_938 = erased
-- Once.LinCore.FromIR.blk?
d_blk'63'_956 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_616 ->
  Maybe MAlonzo.Code.Once.LinCore.PassTr.T_BlkIR_622
d_blk'63'_956 ~v0 ~v1 v2 v3 v4 = du_blk'63'_956 v2 v3 v4
du_blk'63'_956 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_616 ->
  Maybe MAlonzo.Code.Once.LinCore.PassTr.T_BlkIR_622
du_blk'63'_956 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.LinCore.PassTr.C_id_632
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'id_774)
      MAlonzo.Code.Once.LinCore.PassTr.C__'8728'__640 v4 v6 v7
        -> coe
             MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
             (coe du_blk'63'_956 (coe v4) (coe v1) (coe v6))
             (coe
                (\ v8 ->
                   coe
                     MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                     (coe du_blk'63'_956 (coe v0) (coe v4) (coe v7))
                     (coe
                        (\ v9 ->
                           coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45''8728'_786 v8 v9)))))
      MAlonzo.Code.Once.LinCore.PassTr.C_'10216'_'44'_'10217'_648 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v8 v9
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe du_blk'63'_956 (coe v0) (coe v8) (coe v6))
                    (coe
                       (\ v10 ->
                          coe
                            MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                            (coe du_blk'63'_956 (coe v0) (coe v9) (coe v7))
                            (coe
                               (\ v11 ->
                                  coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe
                                       MAlonzo.Code.Once.LinCore.PassTr.C_i'45'pair_798 v10 v11)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.PassTr.C_fst_654
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'fst_804)
      MAlonzo.Code.Once.LinCore.PassTr.C_snd_660
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'snd_810)
      MAlonzo.Code.Once.LinCore.PassTr.C_inl_666
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'inl_816)
      MAlonzo.Code.Once.LinCore.PassTr.C_inr_672
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'inr_822)
      MAlonzo.Code.Once.LinCore.PassTr.C_case_680 v6 v7
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v8 v9
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe du_blk'63'_956 (coe v8) (coe v1) (coe v6))
                    (coe
                       (\ v10 ->
                          coe
                            MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                            (coe du_blk'63'_956 (coe v9) (coe v1) (coe v7))
                            (coe
                               (\ v11 ->
                                  coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe
                                       MAlonzo.Code.Once.LinCore.PassTr.C_i'45'case_834 v10 v11)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.PassTr.C_terminal_684
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'term_838)
      MAlonzo.Code.Once.LinCore.PassTr.C_initial_688
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'init_842)
      MAlonzo.Code.Once.LinCore.PassTr.C_curry_700 v7 v8
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'curry_856)
      MAlonzo.Code.Once.LinCore.PassTr.C_apply_708
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.LinCore.Core.C_Fn_190 v8 v9 v10 v11
                      -> case coe v9 of
                           MAlonzo.Code.Once.LinCore.Core.C_act_158
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                  (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'apply_862)
                           MAlonzo.Code.Once.LinCore.Core.C_eff_160
                             -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.PassTr.C_In_712
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'In_866)
      MAlonzo.Code.Once.LinCore.PassTr.C_out'45'μ_716
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'out_870)
      MAlonzo.Code.Once.LinCore.PassTr.C_Cata_724 v6
        -> case coe v0 of
             MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v7 v8
               -> case coe v8 of
                    MAlonzo.Code.Once.LinCore.Core.C_μt_194 v9
                      -> coe
                           MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                           (coe
                              du_blk'63'_956
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
                                   (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'cata_880 v10)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.PassTr.C_Ana_734 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'ana_892)
      MAlonzo.Code.Once.LinCore.PassTr.C_Out_738
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'Out_896)
      MAlonzo.Code.Once.LinCore.PassTr.C_in'45'ν_742
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'inν_900)
      MAlonzo.Code.Once.LinCore.PassTr.C_Iter_752 v6 v7
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.LinCore.PassTr.C_const_756 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'const_906)
      MAlonzo.Code.Once.LinCore.PassTr.C_SigOp_760 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'op_910)
      MAlonzo.Code.Once.LinCore.PassTr.C_Call_770 v3 v4 v7
        -> case coe v4 of
             MAlonzo.Code.Once.LinCore.Core.C_act_158
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe MAlonzo.Code.Once.LinCore.PassTr.C_i'45'call_920)
             MAlonzo.Code.Once.LinCore.Core.C_eff_160
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.gd?
d_gd'63'_1030 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_616 -> Maybe AgdaAny
d_gd'63'_1030 ~v0 ~v1 v2 v3 v4 v5 = du_gd'63'_1030 v2 v3 v4 v5
du_gd'63'_1030 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_616 -> Maybe AgdaAny
du_gd'63'_1030 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.LinCore.Core.C_act_158
        -> coe du_blk'63'_956 (coe v0) (coe v1) (coe v3)
      MAlonzo.Code.Once.LinCore.Core.C_eff_160
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.Hit
d_Hit_1042 a0 a1 a2 a3 = ()
data T_Hit_1042
  = C_hit_1062 Integer MAlonzo.Code.Once.LinCore.Core.T_Gr_156
               MAlonzo.Code.Once.LinCore.Core.T__'8715''91'_'93'__738
-- Once.LinCore.FromIR.Hit.l
d_l_1056 :: T_Hit_1042 -> Integer
d_l_1056 v0
  = case coe v0 of
      C_hit_1062 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.Hit.g
d_g_1058 :: T_Hit_1042 -> MAlonzo.Code.Once.LinCore.Core.T_Gr_156
d_g_1058 v0
  = case coe v0 of
      C_hit_1062 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.Hit.p
d_p_1060 ::
  T_Hit_1042 ->
  MAlonzo.Code.Once.LinCore.Core.T__'8715''91'_'93'__738
d_p_1060 v0
  = case coe v0 of
      C_hit_1062 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.Resolver
d_Resolver_1064 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 -> ()
d_Resolver_1064 = erased
-- Once.LinCore.FromIR.unlinked-i
d_unlinked'45'i_1072 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
d_unlinked'45'i_1072 ~v0 = du_unlinked'45'i_1072
du_unlinked'45'i_1072 ::
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_102
du_unlinked'45'i_1072
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
d_unlinked_1080 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_616
d_unlinked_1080 ~v0 ~v1 ~v2 ~v3 = du_unlinked_1080
du_unlinked_1080 :: MAlonzo.Code.Once.LinCore.PassTr.T_IR_616
du_unlinked_1080
  = coe
      MAlonzo.Code.Once.LinCore.PassTr.C__'8728'__640
      (coe MAlonzo.Code.Once.LinCore.Core.C_Zero_182)
      (coe MAlonzo.Code.Once.LinCore.PassTr.C_initial_688)
      (coe
         MAlonzo.Code.Once.LinCore.PassTr.C__'8728'__640
         (coe
            MAlonzo.Code.Once.LinCore.Core.du_'8988'_'8989'_532
            (coe
               MAlonzo.Code.Once.LinCore.Core.du_sdom_696
               (coe
                  MAlonzo.Code.Once.LinCore.Core.C_sig_694
                  (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
                  (coe MAlonzo.Code.Once.Spec.Type.C_Void_20)
                  (coe du_unlinked'45'i_1072))))
         (coe
            MAlonzo.Code.Once.LinCore.PassTr.C_SigOp_760
            (coe
               MAlonzo.Code.Once.LinCore.Core.C_sig_694
               (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18)
               (coe MAlonzo.Code.Once.Spec.Type.C_Void_20)
               (coe du_unlinked'45'i_1072)))
         (coe MAlonzo.Code.Once.LinCore.PassTr.C_terminal_684))
-- Once.LinCore.FromIR._.trI
d_trI_1094 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1042) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.LinCore.PassTr.T_IR_616
d_trI_1094 v0 ~v1 v2 v3 v4 v5 = du_trI_1094 v0 v2 v3 v4 v5
du_trI_1094 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1042) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Maybe MAlonzo.Code.Once.LinCore.PassTr.T_IR_616
du_trI_1094 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_id_632)
      MAlonzo.Code.Once.IR.C__'8728'__28 v6 v8 v9
        -> coe
             MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
             (coe du_trI_1094 (coe v0) (coe v1) (coe v6) (coe v3) (coe v8))
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                     (coe du_trI_1094 (coe v0) (coe v1) (coe v2) (coe v6) (coe v9))
                     (coe
                        (\ v11 ->
                           coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe
                                MAlonzo.Code.Once.LinCore.PassTr.C__'8728'__640
                                (d_'10218'_'10219'_840 (coe v0) (coe v6)) v10 v11)))))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v8 v9
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe du_trI_1094 (coe v0) (coe v1) (coe v2) (coe v10) (coe v8))
                    (coe
                       (\ v12 ->
                          coe
                            MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                            (coe du_trI_1094 (coe v0) (coe v1) (coe v2) (coe v11) (coe v9))
                            (coe
                               (\ v13 ->
                                  coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe
                                       MAlonzo.Code.Once.LinCore.PassTr.C_'10216'_'44'_'10217'_648
                                       v12 v13)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_fst_654)
      MAlonzo.Code.Once.IR.C_snd_48
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_snd_660)
      MAlonzo.Code.Once.IR.C_inl_54
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_inl_666)
      MAlonzo.Code.Once.IR.C_inr_60
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_inr_672)
      MAlonzo.Code.Once.IR.C_case_68 v8 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v10 v11
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe du_trI_1094 (coe v0) (coe v1) (coe v10) (coe v3) (coe v8))
                    (coe
                       (\ v12 ->
                          coe
                            MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                            (coe du_trI_1094 (coe v0) (coe v1) (coe v11) (coe v3) (coe v9))
                            (coe
                               (\ v13 ->
                                  coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe MAlonzo.Code.Once.LinCore.PassTr.C_case_680 v12 v13)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_terminal_684)
      MAlonzo.Code.Once.IR.C_initial_76
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_initial_688)
      MAlonzo.Code.Once.IR.C_curry_86 v9
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24 v10 v11 v12
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe
                       du_trI_1094 (coe v0) (coe v1)
                       (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v2) (coe v10))
                       (coe v12) (coe v9))
                    (coe
                       (\ v13 ->
                          coe
                            MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                            (coe
                               du_gd'63'_1030
                               (coe
                                  d_'10218'_'10219'_840 (coe v0)
                                  (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v2) (coe v10)))
                               (coe d_'10218'_'10219'_840 (coe v0) (coe v12))
                               (coe du_grade_838 (coe v11)) (coe v13))
                            (coe
                               (\ v14 ->
                                  coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe MAlonzo.Code.Once.LinCore.PassTr.C_curry_700 v13 v14)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_94
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_apply_708)
      MAlonzo.Code.Once.IR.C_In_98 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_In_712)
      MAlonzo.Code.Once.IR.C_out'45'μ_102 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_out'45'μ_716)
      MAlonzo.Code.Once.IR.C_Cata_110 v6 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> case coe v11 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v12
                      -> coe
                           MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                           (coe
                              du_trI_1094 (coe v0) (coe v1)
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
                                   (coe MAlonzo.Code.Once.LinCore.PassTr.C_Cata_724 v13)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_114 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_Out_738)
      MAlonzo.Code.Once.IR.C_in'45'ν_118 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Once.LinCore.PassTr.C_in'45'ν_742)
      MAlonzo.Code.Once.IR.C_Ana_126 v6 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> case coe v3 of
                    MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v12
                      -> coe
                           MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                           (coe
                              du_trI_1094 (coe v0) (coe v1) (coe v2)
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90 (coe v12) (coe v11))
                              (coe v9))
                           (coe
                              (\ v13 ->
                                 coe
                                   MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                                   (coe
                                      du_blk'63'_956
                                      (coe
                                         MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                                         (coe d_'10218'_'10219'_840 (coe v0) (coe v10))
                                         (coe d_'10218'_'10219'_840 (coe v0) (coe v11)))
                                      (coe
                                         MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198
                                         (coe d_lf_842 (coe v0) (coe v12))
                                         (coe d_'10218'_'10219'_840 (coe v0) (coe v11)))
                                      (coe v13))
                                   (coe
                                      (\ v14 ->
                                         coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe
                                              MAlonzo.Code.Once.LinCore.PassTr.C_Ana_734 v13
                                              v14)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Iter_134 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
               -> coe
                    MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                    (coe
                       du_trI_1094 (coe v0) (coe v1) (coe v2)
                       (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v3) (coe v10))
                       (coe v8))
                    (coe
                       (\ v11 ->
                          coe
                            MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                            (coe
                               du_blk'63'_956 (coe d_'10218'_'10219'_840 (coe v0) (coe v2))
                               (coe
                                  d_'10218'_'10219'_840 (coe v0)
                                  (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v3) (coe v10)))
                               (coe v11))
                            (coe
                               (\ v12 ->
                                  coe
                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                    (coe MAlonzo.Code.Once.LinCore.PassTr.C_Iter_752 v11 v12)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_138 v6 v7
        -> coe
             seq (coe v6)
             (coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Once.LinCore.PassTr.C_const_756 v7))
      MAlonzo.Code.Once.IR.C_SigOp_144 v5 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                MAlonzo.Code.Once.LinCore.PassTr.C_SigOp_760
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_sig_694 (coe v5) (coe v6)
                   (coe v7)))
      MAlonzo.Code.Once.IR.C_Call_150 v7
        -> let v8 = coe v1 v7 v2 v3 in
           coe
             (case coe v8 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                  -> case coe v9 of
                       C_hit_1062 v10 v11 v12
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe MAlonzo.Code.Once.LinCore.PassTr.C_Call_770 v10 v11 v12)
                       _ -> MAlonzo.RTE.mazUnreachableError
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe du_unlinked_1080)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.TrProg
d_TrProg_1228 a0 = ()
data T_TrProg_1228
  = C_trProg_1242 MAlonzo.Code.Once.LinCore.Core.T_Cx_728
                  MAlonzo.Code.Once.LinCore.PassTr.T_Prog_1190
                  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
                   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
                   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1042)
-- Once.LinCore.FromIR.TrProg.Γ
d_Γ_1236 ::
  T_TrProg_1228 -> MAlonzo.Code.Once.LinCore.Core.T_Cx_728
d_Γ_1236 v0
  = case coe v0 of
      C_trProg_1242 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.TrProg.prog
d_prog_1238 ::
  T_TrProg_1228 -> MAlonzo.Code.Once.LinCore.PassTr.T_Prog_1190
d_prog_1238 v0
  = case coe v0 of
      C_trProg_1242 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.TrProg.rs
d_rs_1240 ::
  T_TrProg_1228 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1042
d_rs_1240 v0
  = case coe v0 of
      C_trProg_1242 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.weaken
d_weaken_1252 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  T_Hit_1042 -> T_Hit_1042
d_weaken_1252 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_weaken_1252 v5
du_weaken_1252 :: T_Hit_1042 -> T_Hit_1042
du_weaken_1252 v0
  = case coe v0 of
      C_hit_1062 v1 v2 v3
        -> coe
             C_hit_1062 (coe v1) (coe v2)
             (coe MAlonzo.Code.Once.LinCore.Core.C_there_754 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.extend-at
d_extend'45'at_1272 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1042) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_Hit_1042
d_extend'45'at_1272 ~v0 v1 v2 v3 ~v4 v5 v6 v7 v8 v9 v10
  = du_extend'45'at_1272 v1 v2 v3 v5 v6 v7 v8 v9 v10
du_extend'45'at_1272 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1042) ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe T_Hit_1042
du_extend'45'at_1272 v0 v1 v2 v3 v4 v5 v6 v7 v8
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
                                                            C_hit_1062
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
                                                         (coe du_weaken_1252) (coe v2 v3 v4 v5))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              else coe
                                     seq (coe v12)
                                     (coe
                                        MAlonzo.Code.Data.Maybe.Base.du_map_64 (coe du_weaken_1252)
                                        (coe v2 v3 v4 v5))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe
                    seq (coe v10)
                    (coe
                       MAlonzo.Code.Data.Maybe.Base.du_map_64 (coe du_weaken_1252)
                       (coe v2 v3 v4 v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.extend
d_extend_1338 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1042) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1042
d_extend_1338 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_extend_1338 v1 v2 v3 v4 v5 v6 v7
du_extend_1338 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1042) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1042
du_extend_1338 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_extend'45'at_1272 (coe v0) (coe v1) (coe v2) (coe v4) (coe v5)
      (coe v6)
      (coe
         MAlonzo.Code.Once.CanonicalName.d__'8799''7580'__4
         (coe MAlonzo.Code.Once.Denotation.Program.d_fname_16 (coe v3))
         (coe v4))
      (coe
         MAlonzo.Code.Once.IRTy.d__'8799'IRTy__206
         (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v3))
         (coe v5))
      (coe
         MAlonzo.Code.Once.IRTy.d__'8799'IRTy__206
         (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v3))
         (coe v6))
-- Once.LinCore.FromIR.entry-at
d_entry'45'at_1358 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_Prog_1190 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1042) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_616 ->
  Maybe MAlonzo.Code.Once.LinCore.PassTr.T_BlkIR_622 -> T_TrProg_1228
d_entry'45'at_1358 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> coe
             C_trProg_1242
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'9656'__732 (coe v1)
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_sg_726
                   (coe MAlonzo.Code.Once.LinCore.Core.C_once_152)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_act_158)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                   (coe
                      d_'10218'_'10219'_840 (coe v0)
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v4)))
                   (coe
                      d_'10218'_'10219'_840 (coe v0)
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v4)))))
             (coe
                MAlonzo.Code.Once.LinCore.PassTr.C__'9657'_'8739'__1204 v2 v5 v7)
             (coe
                du_extend_1338 (coe v1)
                (coe MAlonzo.Code.Once.LinCore.Core.C_act_158) (coe v3) (coe v4))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             C_trProg_1242
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'9656'__732 (coe v1)
                (coe
                   MAlonzo.Code.Once.LinCore.Core.C_sg_726
                   (coe MAlonzo.Code.Once.LinCore.Core.C_once_152)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_eff_160)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                   (coe
                      d_'10218'_'10219'_840 (coe v0)
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v4)))
                   (coe
                      d_'10218'_'10219'_840 (coe v0)
                      (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v4)))))
             (coe
                MAlonzo.Code.Once.LinCore.PassTr.C__'9657'_'8739'__1204 v2 v5
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             (coe
                du_extend_1338 (coe v1)
                (coe MAlonzo.Code.Once.LinCore.Core.C_eff_160) (coe v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR.entry
d_entry_1382 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_Prog_1190 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1042) ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_616 -> T_TrProg_1228
d_entry_1382 v0 v1 v2 v3 v4 v5
  = coe
      d_entry'45'at_1358 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5)
      (coe
         du_blk'63'_956
         (coe
            d_'10218'_'10219'_840 (coe v0)
            (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v4)))
         (coe
            d_'10218'_'10219'_840 (coe v0)
            (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v4)))
         (coe v5))
-- Once.LinCore.FromIR.trTable
d_trTable_1392 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6] ->
  Maybe T_TrProg_1228
d_trTable_1392 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe
                C_trProg_1242 (coe MAlonzo.Code.Once.LinCore.Core.C_ε_730)
                (coe MAlonzo.Code.Once.LinCore.PassTr.C_ε_1192)
                (coe
                   (\ v2 v3 v4 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
             (coe d_trTable_1392 (coe v0) (coe v3))
             (coe
                (\ v4 ->
                   coe
                     MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
                     (coe
                        du_trI_1094 (coe v0) (coe d_rs_1240 (coe v4))
                        (coe MAlonzo.Code.Once.Denotation.Program.d_fdom_18 (coe v2))
                        (coe MAlonzo.Code.Once.Denotation.Program.d_fcod_20 (coe v2))
                        (coe MAlonzo.Code.Once.Denotation.Program.d_fbody_22 (coe v2)))
                     (coe
                        (\ v5 ->
                           coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe
                                d_entry_1382 (coe v0) (coe d_Γ_1236 (coe v4))
                                (coe d_prog_1238 (coe v4)) (coe d_rs_1240 (coe v4)) (coe v2)
                                (coe v5))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR._.Tr
d_Tr_1420 a0 a1 a2 a3 a4 a5 a6 = ()
data T_Tr_1420
  = C_t'45'id_1424 | C_t'45''8728'_1440 T_Tr_1420 T_Tr_1420 |
    C_t'45'pair_1456 T_Tr_1420 T_Tr_1420 | C_t'45'fst_1462 |
    C_t'45'snd_1468 | C_t'45'inl_1474 | C_t'45'inr_1480 |
    C_t'45'case_1496 T_Tr_1420 T_Tr_1420 | C_t'45'term_1500 |
    C_t'45'init_1504 | C_t'45'curry_1520 T_Tr_1420 |
    C_t'45'apply_1528 | C_t'45'In_1536 | C_t'45'out_1544 |
    C_t'45'cata_1560 MAlonzo.Code.Once.LinCore.PassTr.T_IR_616
                     T_Tr_1420 |
    C_t'45'Out_1568 | C_t'45'inν_1576 |
    C_t'45'ana_1594 MAlonzo.Code.Once.LinCore.PassTr.T_IR_616
                    T_Tr_1420 |
    C_t'45'iter_1608 T_Tr_1420 | C_t'45'int_1612 | C_t'45'float_1616 |
    C_t'45'op_1624 | C_t'45'hit_1638 | C_t'45'miss_1646
-- Once.LinCore.FromIR._.bind-just
d_bind'45'just_1660 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1042) ->
  () ->
  () ->
  Maybe AgdaAny ->
  (AgdaAny -> Maybe AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bind'45'just_1660 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8
  = du_bind'45'just_1660 v5 v8
du_bind'45'just_1660 ::
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bind'45'just_1660 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.FromIR._.trI-Tr
d_trI'45'Tr_1674 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1042) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.LinCore.PassTr.T_IR_616 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T_Tr_1420
d_trI'45'Tr_1674 v0 ~v1 v2 v3 v4 v5 ~v6 ~v7
  = du_trI'45'Tr_1674 v0 v2 v3 v4 v5
du_trI'45'Tr_1674 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 -> Maybe T_Hit_1042) ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> T_Tr_1420
du_trI'45'Tr_1674 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.IR.C_id_20 -> coe C_t'45'id_1424
      MAlonzo.Code.Once.IR.C__'8728'__28 v6 v8 v9
        -> let v10
                 = coe
                     du_bind'45'just_1660
                     (coe du_trI_1094 (coe v0) (coe v1) (coe v6) (coe v3) (coe v8))
                     erased in
           coe
             (case coe v10 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                  -> coe
                       seq (coe v12)
                       (let v13
                              = coe
                                  du_bind'45'just_1660
                                  (coe du_trI_1094 (coe v0) (coe v1) (coe v2) (coe v6) (coe v9))
                                  erased in
                        coe
                          (case coe v13 of
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                               -> coe
                                    seq (coe v15)
                                    (coe
                                       C_t'45''8728'_1440
                                       (coe
                                          du_trI'45'Tr_1674 (coe v0) (coe v1) (coe v6) (coe v3)
                                          (coe v8))
                                       (coe
                                          du_trI'45'Tr_1674 (coe v0) (coe v1) (coe v2) (coe v6)
                                          (coe v9)))
                             _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v8 v9
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> let v12
                        = coe
                            du_bind'45'just_1660
                            (coe du_trI_1094 (coe v0) (coe v1) (coe v2) (coe v10) (coe v8))
                            erased in
                  coe
                    (case coe v12 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                         -> coe
                              seq (coe v14)
                              (let v15
                                     = coe
                                         du_bind'45'just_1660
                                         (coe
                                            du_trI_1094 (coe v0) (coe v1) (coe v2) (coe v11)
                                            (coe v9))
                                         erased in
                               coe
                                 (case coe v15 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                      -> coe
                                           seq (coe v17)
                                           (coe
                                              C_t'45'pair_1456
                                              (coe
                                                 du_trI'45'Tr_1674 (coe v0) (coe v1) (coe v2)
                                                 (coe v10) (coe v8))
                                              (coe
                                                 du_trI'45'Tr_1674 (coe v0) (coe v1) (coe v2)
                                                 (coe v11) (coe v9)))
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42 -> coe C_t'45'fst_1462
      MAlonzo.Code.Once.IR.C_snd_48 -> coe C_t'45'snd_1468
      MAlonzo.Code.Once.IR.C_inl_54 -> coe C_t'45'inl_1474
      MAlonzo.Code.Once.IR.C_inr_60 -> coe C_t'45'inr_1480
      MAlonzo.Code.Once.IR.C_case_68 v8 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v10 v11
               -> let v12
                        = coe
                            du_bind'45'just_1660
                            (coe du_trI_1094 (coe v0) (coe v1) (coe v10) (coe v3) (coe v8))
                            erased in
                  coe
                    (case coe v12 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                         -> coe
                              seq (coe v14)
                              (let v15
                                     = coe
                                         du_bind'45'just_1660
                                         (coe
                                            du_trI_1094 (coe v0) (coe v1) (coe v11) (coe v3)
                                            (coe v9))
                                         erased in
                               coe
                                 (case coe v15 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                      -> coe
                                           seq (coe v17)
                                           (coe
                                              C_t'45'case_1496
                                              (coe
                                                 du_trI'45'Tr_1674 (coe v0) (coe v1) (coe v10)
                                                 (coe v3) (coe v8))
                                              (coe
                                                 du_trI'45'Tr_1674 (coe v0) (coe v1) (coe v11)
                                                 (coe v3) (coe v9)))
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72 -> coe C_t'45'term_1500
      MAlonzo.Code.Once.IR.C_initial_76 -> coe C_t'45'init_1504
      MAlonzo.Code.Once.IR.C_curry_86 v9
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24 v10 v11 v12
               -> let v13
                        = coe
                            du_bind'45'just_1660
                            (coe
                               du_trI_1094 (coe v0) (coe v1)
                               (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v2) (coe v10))
                               (coe v12) (coe v9))
                            erased in
                  coe
                    (case coe v13 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                         -> coe
                              seq (coe v15)
                              (let v16
                                     = coe
                                         du_bind'45'just_1660
                                         (coe
                                            du_gd'63'_1030
                                            (coe
                                               MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                                               (coe d_'10218'_'10219'_840 (coe v0) (coe v2))
                                               (coe d_'10218'_'10219'_840 (coe v0) (coe v10)))
                                            (coe d_'10218'_'10219'_840 (coe v0) (coe v12))
                                            (coe du_grade_838 (coe v11)) (coe v14))
                                         erased in
                               coe
                                 (case coe v16 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                      -> coe
                                           seq (coe v18)
                                           (coe
                                              C_t'45'curry_1520
                                              (coe
                                                 du_trI'45'Tr_1674 (coe v0) (coe v1)
                                                 (coe
                                                    MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v2)
                                                    (coe v10))
                                                 (coe v12) (coe v9)))
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_94 -> coe C_t'45'apply_1528
      MAlonzo.Code.Once.IR.C_In_98 v6 -> coe C_t'45'In_1536
      MAlonzo.Code.Once.IR.C_out'45'μ_102 v6 -> coe C_t'45'out_1544
      MAlonzo.Code.Once.IR.C_Cata_110 v6 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> case coe v11 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v12
                      -> let v13
                               = coe
                                   du_bind'45'just_1660
                                   (coe
                                      du_trI_1094 (coe v0) (coe v1)
                                      (coe
                                         MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v10)
                                         (coe
                                            MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90 (coe v12)
                                            (coe v3)))
                                      (coe v3) (coe v9))
                                   erased in
                         coe
                           (case coe v13 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                -> coe
                                     seq (coe v15)
                                     (coe
                                        C_t'45'cata_1560 v14
                                        (coe
                                           du_trI'45'Tr_1674 (coe v0) (coe v1)
                                           (coe
                                              MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v10)
                                              (coe
                                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                                 (coe v12) (coe v3)))
                                           (coe v3) (coe v9)))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_114 v6 -> coe C_t'45'Out_1568
      MAlonzo.Code.Once.IR.C_in'45'ν_118 v6 -> coe C_t'45'inν_1576
      MAlonzo.Code.Once.IR.C_Ana_126 v6 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> case coe v3 of
                    MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v12
                      -> let v13
                               = coe
                                   du_bind'45'just_1660
                                   (coe
                                      du_trI_1094 (coe v0) (coe v1) (coe v2)
                                      (coe
                                         MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90 (coe v12)
                                         (coe v11))
                                      (coe v9))
                                   erased in
                         coe
                           (case coe v13 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                -> coe
                                     seq (coe v15)
                                     (let v16
                                            = coe
                                                du_bind'45'just_1660
                                                (coe
                                                   du_blk'63'_956
                                                   (coe
                                                      MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                                                      (coe d_'10218'_'10219'_840 (coe v0) (coe v10))
                                                      (coe
                                                         d_'10218'_'10219'_840 (coe v0) (coe v11)))
                                                   (coe
                                                      MAlonzo.Code.Once.LinCore.Core.du_LF'8729'_198
                                                      (coe d_lf_842 (coe v0) (coe v12))
                                                      (coe
                                                         d_'10218'_'10219'_840 (coe v0) (coe v11)))
                                                   (coe v14))
                                                erased in
                                      coe
                                        (case coe v16 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                             -> coe
                                                  seq (coe v18)
                                                  (coe
                                                     C_t'45'ana_1594 v14
                                                     (coe
                                                        du_trI'45'Tr_1674 (coe v0) (coe v1) (coe v2)
                                                        (coe
                                                           MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_90
                                                           (coe v12) (coe v11))
                                                        (coe v9)))
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Iter_134 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v9 v10
               -> let v11
                        = coe
                            du_bind'45'just_1660
                            (coe
                               du_trI_1094 (coe v0) (coe v1) (coe v2)
                               (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v3) (coe v10))
                               (coe v8))
                            erased in
                  coe
                    (case coe v11 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                         -> coe
                              seq (coe v13)
                              (let v14
                                     = coe
                                         du_bind'45'just_1660
                                         (coe
                                            du_blk'63'_956
                                            (coe
                                               MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                                               (coe d_'10218'_'10219'_840 (coe v0) (coe v9))
                                               (coe d_'10218'_'10219'_840 (coe v0) (coe v10)))
                                            (coe
                                               MAlonzo.Code.Once.LinCore.Core.C__'8853't__186
                                               (coe d_'10218'_'10219'_840 (coe v0) (coe v3))
                                               (coe d_'10218'_'10219'_840 (coe v0) (coe v10)))
                                            (coe v12))
                                         erased in
                               coe
                                 (case coe v14 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                      -> coe
                                           seq (coe v16)
                                           (coe
                                              C_t'45'iter_1608
                                              (coe
                                                 du_trI'45'Tr_1674 (coe v0) (coe v1) (coe v2)
                                                 (coe
                                                    MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v3)
                                                    (coe v10))
                                                 (coe v8)))
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_138 v6 v7
        -> case coe v6 of
             MAlonzo.Code.Once.IRTy.C_fits'45'int_554 -> coe C_t'45'int_1612
             MAlonzo.Code.Once.IRTy.C_fits'45'float_556 -> coe C_t'45'float_1616
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_SigOp_144 v5 v6 v7 -> coe C_t'45'op_1624
      MAlonzo.Code.Once.IR.C_Call_150 v7
        -> let v8 = coe v1 v7 v2 v3 in
           coe
             (case coe v8 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                  -> coe seq (coe v9) (coe C_t'45'hit_1638)
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe C_t'45'miss_1646
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
