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

module MAlonzo.Code.Once.LinCore.ExprBuild where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.CompileSrc
import qualified MAlonzo.Code.Once.Context
import qualified MAlonzo.Code.Once.Denotation.Program
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.LinCore.Core
import qualified MAlonzo.Code.Once.LinCore.Flat
import qualified MAlonzo.Code.Once.LinCore.FromExpr
import qualified MAlonzo.Code.Once.LinCore.FromIR
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Spec.Sub
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Once.LinCore.ExprBuild._._∋[_]_
d__'8715''91'_'93'__10 a0 a1 a2 a3 = ()
-- Once.LinCore.ExprBuild._.Blk
d_Blk_30 a0 a1 a2 a3 a4 a5 = ()
-- Once.LinCore.ExprBuild._.Body
d_Body_32 a0 a1 a2 = ()
-- Once.LinCore.ExprBuild._.Cx
d_Cx_40 a0 = ()
-- Once.LinCore.ExprBuild._.Defs
d_Defs_42 a0 a1 = ()
-- Once.LinCore.ExprBuild._.Gd
d_Gd_50 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 -> ()
d_Gd_50 = erased
-- Once.LinCore.ExprBuild._.Gr
d_Gr_52 a0 = ()
-- Once.LinCore.ExprBuild._.Kd
d_Kd_58 a0 = ()
-- Once.LinCore.ExprBuild._.LTm
d_LTm_70 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> ()
d_LTm_70 = erased
-- Once.LinCore.ExprBuild._.LTy
d_LTy_72 a0 = ()
-- Once.LinCore.ExprBuild._.Sg
d_Sg_90 a0 = ()
-- Once.LinCore.ExprBuild._.Tm
d_Tm_98 a0 a1 a2 a3 a4 = ()
-- Once.LinCore.ExprBuild._.Sg.cod
d_cod_592 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_cod_592 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_cod_724 (coe v0)
-- Once.LinCore.ExprBuild._.Sg.dom
d_dom_594 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_dom_594 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_dom_722 (coe v0)
-- Once.LinCore.ExprBuild._.Sg.env
d_env_596 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_env_596 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_env_720 (coe v0)
-- Once.LinCore.ExprBuild._.Sg.gr
d_gr_598 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156
d_gr_598 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_gr_718 (coe v0)
-- Once.LinCore.ExprBuild._.Sg.kd
d_kd_600 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Kd_150
d_kd_600 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_kd_716 (coe v0)
-- Once.LinCore.ExprBuild._.Co
d_Co_696 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_Co_696 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.LinCore.FromExpr.du_Co_724 (coe v0) v1 v3 v4
-- Once.LinCore.ExprBuild._.ty
d_ty_708 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_ty_708 v0
  = coe MAlonzo.Code.Once.LinCore.FromExpr.d_ty_716 (coe v0)
-- Once.LinCore.ExprBuild._.grade
d_grade_712 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156
d_grade_712 ~v0 = du_grade_712
du_grade_712 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156
du_grade_712 = coe MAlonzo.Code.Once.LinCore.FromIR.du_grade_922
-- Once.LinCore.ExprBuild._.⟪_⟫
d_'10218'_'10219'_716 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178
d_'10218'_'10219'_716 v0
  = coe
      MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_924 (coe v0)
-- Once.LinCore.ExprBuild._.Rs
d_Rs_724 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 -> ()
d_Rs_724 = erased
-- Once.LinCore.ExprBuild._.eraseL
d_eraseL_746 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_eraseL_746 v0 ~v1 ~v2 v3 ~v4 v5 v6 = du_eraseL_746 v0 v3 v5 v6
du_eraseL_746 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_eraseL_746 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Context.C_'8709'_12
        -> coe seq (coe v3) (coe MAlonzo.Code.Once.LinCore.Core.C_lid_786)
      MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v5 v6
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v8 v9
               -> case coe v8 of
                    MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                           (MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_924
                              (coe v0)
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe v1)
                                 (coe
                                    MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                    (coe v5))))
                           (coe du_eraseL_746 (coe v0) (coe v1) (coe v5) (coe v9))
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                                 (coe
                                    MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_924 (coe v0)
                                    (coe
                                       MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe v1)
                                       (coe
                                          MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                          (coe v5))))
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180))
                              (coe MAlonzo.Code.Once.LinCore.Core.C_ρl_814)
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_lid_786)
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_drop_872)))
                    MAlonzo.Code.Once.Spec.Grade.C_One_10
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808
                           (coe du_eraseL_746 (coe v0) (coe v1) (coe v5) (coe v9))
                           (coe MAlonzo.Code.Once.LinCore.Core.C_lid_786)
                    MAlonzo.Code.Once.Spec.Grade.C_Many_12
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808
                           (coe du_eraseL_746 (coe v0) (coe v1) (coe v5) (coe v9))
                           (coe MAlonzo.Code.Once.LinCore.Core.C_lid_786)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild._.k-eraseL
d_k'45'eraseL_774 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'eraseL_774 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_k'45'eraseL_774 v5 v6
du_k'45'eraseL_774 ::
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
du_k'45'eraseL_774 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'8709'_12
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1152)
      MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
                           (coe du_k'45'eraseL_774 (coe v3) (coe v7))
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
                              (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'ρ_1188)
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1182
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1152)
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1246)))
                    MAlonzo.Code.Once.Spec.Grade.C_One_10
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1182
                           (coe du_k'45'eraseL_774 (coe v3) (coe v7))
                           (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1152)
                    MAlonzo.Code.Once.Spec.Grade.C_Many_12
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1182
                           (coe du_k'45'eraseL_774 (coe v3) (coe v7))
                           (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1152)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.dcDom
d_dcDom_794 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_dcDom_794 ~v0 v1 = du_dcDom_794 v1
du_dcDom_794 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
du_dcDom_794 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_Unit_18 -> coe v0
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe MAlonzo.Code.Once.Spec.Type.C_Unit_18
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v1 v2
        -> coe MAlonzo.Code.Once.Spec.Type.C_Unit_18
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v1 v2
        -> coe MAlonzo.Code.Once.Spec.Type.C_Unit_18
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v4 v5
               -> case coe v4 of
                    MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                      -> coe MAlonzo.Code.Once.Spec.Type.C_Unit_18
                    MAlonzo.Code.Once.Spec.Grade.C_One_10 -> coe v1
                    MAlonzo.Code.Once.Spec.Grade.C_Many_12 -> coe v1
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v1
        -> coe MAlonzo.Code.Once.Spec.Type.C_Unit_18
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v1 v2
        -> coe MAlonzo.Code.Once.Spec.Type.C_Unit_18
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe MAlonzo.Code.Once.Spec.Type.C_Unit_18
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe MAlonzo.Code.Once.Spec.Type.C_Unit_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.dcCod
d_dcCod_796 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_dcCod_796 ~v0 v1 = du_dcCod_796 v1
du_dcCod_796 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
du_dcCod_796 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_Unit_18 -> coe v0
      MAlonzo.Code.Once.Spec.Type.C_Void_20 -> coe v0
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v1 v2 -> coe v0
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v1 v2 -> coe v0
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v1 v2 v3
        -> coe seq (coe v2) (coe v3)
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v1 -> coe v0
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v1 v2 -> coe v0
      MAlonzo.Code.Once.Spec.Type.C_Int_32 -> coe v0
      MAlonzo.Code.Once.Spec.Type.C_Float_34 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.dcGr
d_dcGr_868 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156
d_dcGr_868 ~v0 v1 = du_dcGr_868 v1
du_dcGr_868 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156
du_dcGr_868 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe MAlonzo.Code.Once.LinCore.Core.C_act_158
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe MAlonzo.Code.Once.LinCore.Core.C_act_158
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v1 v2
        -> coe MAlonzo.Code.Once.LinCore.Core.C_act_158
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v1 v2
        -> coe MAlonzo.Code.Once.LinCore.Core.C_act_158
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v4 v5
               -> coe MAlonzo.Code.Once.LinCore.FromIR.du_grade_922 (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v1
        -> coe MAlonzo.Code.Once.LinCore.Core.C_act_158
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v1 v2
        -> coe MAlonzo.Code.Once.LinCore.Core.C_act_158
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe MAlonzo.Code.Once.LinCore.Core.C_act_158
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe MAlonzo.Code.Once.LinCore.Core.C_act_158
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild._.dc
d_dc_900 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_dc_900 v0 ~v1 v2 v3 = du_dc_900 v0 v2 v3
du_dc_900 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_dc_900 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Spec.Type.C_Unit_18 -> coe v2
      MAlonzo.Code.Once.Spec.Type.C_Void_20 -> coe v2
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v3 v4 -> coe v2
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v3 v4 -> coe v2
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v3 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C_Fn_190
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_many_154)
                                 (coe MAlonzo.Code.Once.LinCore.FromIR.du_grade_922 (coe v7))
                                 (coe
                                    MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_924 (coe v0)
                                    (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
                                 (coe
                                    MAlonzo.Code.Once.LinCore.FromExpr.d_ty_716 (coe v0)
                                    (coe (0 :: Integer)) (coe du_dcCod_796 (coe v1))))
                              (coe
                                 MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_924 (coe v0)
                                 (coe MAlonzo.Code.Once.IRTy.C_Unit_16)))
                           (coe MAlonzo.Code.Once.LinCore.Core.C_levω_1108)
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                                 (coe
                                    MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_924 (coe v0)
                                    (coe MAlonzo.Code.Once.IRTy.C_Unit_16)))
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808 v2
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_lid_786))
                              (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_832))
                    MAlonzo.Code.Once.Spec.Grade.C_One_10
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C_Fn_190
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_many_154)
                                 (coe MAlonzo.Code.Once.LinCore.FromIR.du_grade_922 (coe v7))
                                 (coe
                                    MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_924 (coe v0)
                                    (coe
                                       MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                       (coe (0 :: Integer)) (coe v3)))
                                 (coe
                                    MAlonzo.Code.Once.LinCore.FromExpr.d_ty_716 (coe v0)
                                    (coe (0 :: Integer)) (coe du_dcCod_796 (coe v1))))
                              (coe
                                 MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_924 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe (0 :: Integer))
                                    (coe v3))))
                           (coe MAlonzo.Code.Once.LinCore.Core.C_levω_1108)
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                                 (coe
                                    MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_924 (coe v0)
                                    (coe
                                       MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                       (coe (0 :: Integer)) (coe v3))))
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808 v2
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_lid_786))
                              (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_832))
                    MAlonzo.Code.Once.Spec.Grade.C_Many_12
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C_Fn_190
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_many_154)
                                 (coe MAlonzo.Code.Once.LinCore.FromIR.du_grade_922 (coe v7))
                                 (coe
                                    MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_924 (coe v0)
                                    (coe
                                       MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                       (coe (0 :: Integer)) (coe v3)))
                                 (coe
                                    MAlonzo.Code.Once.LinCore.FromExpr.d_ty_716 (coe v0)
                                    (coe (0 :: Integer)) (coe du_dcCod_796 (coe v1))))
                              (coe
                                 MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_924 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe (0 :: Integer))
                                    (coe v3))))
                           (coe MAlonzo.Code.Once.LinCore.Core.C_levω_1108)
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855't__184
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                                 (coe
                                    MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_924 (coe v0)
                                    (coe
                                       MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                       (coe (0 :: Integer)) (coe v3))))
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855'l__808 v2
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_lid_786))
                              (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_832))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v3 -> coe v2
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v3 v4 -> coe v2
      MAlonzo.Code.Once.Spec.Type.C_Int_32 -> coe v2
      MAlonzo.Code.Once.Spec.Type.C_Float_34 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild._.gdT
d_gdT_968 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  (MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.LinCore.Core.T_Blk_768) ->
  AgdaAny
d_gdT_968 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 = du_gdT_968 v4 v6
du_gdT_968 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  (MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.LinCore.Core.T_Blk_768) ->
  AgdaAny
du_gdT_968 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v2 -> coe v1 v2 erased
      MAlonzo.Code.Once.Spec.Grade.C_eff_44
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild._.dcGd
d_dcGd_984 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 -> AgdaAny
d_dcGd_984 ~v0 ~v1 v2 ~v3 v4 = du_dcGd_984 v2 v4
du_dcGd_984 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768 -> AgdaAny
du_dcGd_984 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166 v1
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1200)
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166 v1
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1200)
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166 v1
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1200)
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166 v1
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1200)
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v2 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v5 v6
               -> coe
                    seq (coe v5)
                    (coe
                       du_gdT_968 (coe v6)
                       (coe
                          (\ v7 v8 ->
                             coe
                               MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
                               (coe
                                  MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
                                  (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'evω_1504)
                                  (coe
                                     MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
                                     (coe
                                        MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1182 v1
                                        (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1152))
                                     (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1206)))
                               (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1200))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v2
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166 v1
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1200)
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166 v1
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1200)
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166 v1
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1200)
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166 v1
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1200)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.dcIR
d_dcIR_1060 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_dcIR_1060 ~v0 v1 v2 = du_dcIR_1060 v1 v2
du_dcIR_1060 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_dcIR_1060 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_Unit_18 -> coe v1
      MAlonzo.Code.Once.Spec.Type.C_Void_20 -> coe v1
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v2 v3 -> coe v1
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v2 v3 -> coe v1
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v2 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v5 v6
               -> case coe v5 of
                    MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                      -> coe
                           MAlonzo.Code.Once.IR.C__'8728'__28
                           (coe
                              MAlonzo.Code.Once.IRTy.C__'42'__20
                              (coe
                                 MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24
                                 (coe MAlonzo.Code.Once.IRTy.C_Unit_16) (coe v6)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe (0 :: Integer))
                                    (coe du_dcCod_796 (coe v0))))
                              (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
                           (coe MAlonzo.Code.Once.IR.C_apply_94)
                           (coe
                              MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                              (coe
                                 MAlonzo.Code.Once.IR.C__'8728'__28
                                 (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                    (coe (0 :: Integer))
                                    (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18))
                                 v1 (coe MAlonzo.Code.Once.IR.C_terminal_72))
                              (coe MAlonzo.Code.Once.IR.C_id_20))
                    MAlonzo.Code.Once.Spec.Grade.C_One_10
                      -> coe
                           MAlonzo.Code.Once.IR.C__'8728'__28
                           (coe
                              MAlonzo.Code.Once.IRTy.C__'42'__20
                              (coe
                                 MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe (0 :: Integer))
                                    (coe v2))
                                 (coe v6)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe (0 :: Integer))
                                    (coe du_dcCod_796 (coe v0))))
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe (0 :: Integer))
                                 (coe v2)))
                           (coe MAlonzo.Code.Once.IR.C_apply_94)
                           (coe
                              MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                              (coe
                                 MAlonzo.Code.Once.IR.C__'8728'__28
                                 (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                    (coe (0 :: Integer))
                                    (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18))
                                 v1 (coe MAlonzo.Code.Once.IR.C_terminal_72))
                              (coe MAlonzo.Code.Once.IR.C_id_20))
                    MAlonzo.Code.Once.Spec.Grade.C_Many_12
                      -> coe
                           MAlonzo.Code.Once.IR.C__'8728'__28
                           (coe
                              MAlonzo.Code.Once.IRTy.C__'42'__20
                              (coe
                                 MAlonzo.Code.Once.IRTy.C__'8667''91'_'93'__24
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe (0 :: Integer))
                                    (coe v2))
                                 (coe v6)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe (0 :: Integer))
                                    (coe du_dcCod_796 (coe v0))))
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe (0 :: Integer))
                                 (coe v2)))
                           (coe MAlonzo.Code.Once.IR.C_apply_94)
                           (coe
                              MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36
                              (coe
                                 MAlonzo.Code.Once.IR.C__'8728'__28
                                 (MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                    (coe (0 :: Integer))
                                    (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18))
                                 v1 (coe MAlonzo.Code.Once.IR.C_terminal_72))
                              (coe MAlonzo.Code.Once.IR.C_id_20))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v2 -> coe v1
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v2 v3 -> coe v1
      MAlonzo.Code.Once.Spec.Type.C_Int_32 -> coe v1
      MAlonzo.Code.Once.Spec.Type.C_Float_34 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.dc-eq
d_dc'45'eq_1122 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_dc'45'eq_1122 = erased
-- Once.LinCore.ExprBuild.val
d_val_1184 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.CompileSrc.T_Src_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_val_1184 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.CompileSrc.C_src_38 v5 v6 v7 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
             (coe
                MAlonzo.Code.Once.LinCore.FromExpr.du_Co_724 (coe v0)
                (coe (0 :: Integer)) (coe v6) (coe v7))
             (MAlonzo.Code.Once.LinCore.FromExpr.d_Lq_3664
                (coe v0) (coe v1) (coe v3) (coe (0 :: Integer)) (coe v5) (coe v6)
                (coe v7) (coe v2) (coe v11))
             (coe du_eraseL_746 (coe v0) (coe (0 :: Integer)) (coe v6) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.k-val
d_k'45'val_1208 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.CompileSrc.T_Src_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_768
d_k'45'val_1208 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.CompileSrc.C_src_38 v5 v6 v7 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1166
             (coe
                MAlonzo.Code.Once.LinCore.FromExpr.du_Lq'45'blk_3678 (coe v0)
                (coe v1) (coe v3) (coe (0 :: Integer)) (coe v5) (coe v6) (coe v2)
                (coe v11))
             (coe du_k'45'eraseL_774 (coe v6) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.sgOf
d_sgOf_1224 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012 ->
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704
d_sgOf_1224 v0 v1
  = coe
      MAlonzo.Code.Once.LinCore.Core.C_sg_726
      (coe MAlonzo.Code.Once.LinCore.Core.C_once_152)
      (coe
         du_dcGr_868
         (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v1)))
      (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
      (coe
         MAlonzo.Code.Once.LinCore.FromExpr.d_ty_716 (coe v0)
         (coe (0 :: Integer))
         (coe
            du_dcDom_794
            (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v1))))
      (coe
         MAlonzo.Code.Once.LinCore.FromExpr.d_ty_716 (coe v0)
         (coe (0 :: Integer))
         (coe
            du_dcCod_796
            (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v1))))
-- Once.LinCore.ExprBuild.bodyOf
d_bodyOf_1234 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012 ->
  MAlonzo.Code.Once.LinCore.Core.T_Body_2118
d_bodyOf_1234 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.LinCore.Core.C_b1_2132
      (coe
         MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
         (MAlonzo.Code.Once.LinCore.FromExpr.d_ty_716
            (coe v0) (coe (0 :: Integer))
            (coe
               du_dcDom_794
               (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v3))))
         (coe
            du_dc_900 (coe v0)
            (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v3))
            (coe
               d_val_1184 (coe v0) (coe v1)
               (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v3)) (coe v2)
               (coe MAlonzo.Code.Once.CompileSrc.d_csSrc_1024 (coe v3))))
         (coe MAlonzo.Code.Once.LinCore.Core.C_lul_826))
      (coe
         du_dcGd_984
         (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v3))
         (coe
            d_k'45'val_1208 (coe v0) (coe v1)
            (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v3)) (coe v2)
            (coe MAlonzo.Code.Once.CompileSrc.d_csSrc_1024 (coe v3))))
-- Once.LinCore.ExprBuild._≟Gr_
d__'8799'Gr__1244 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'Gr__1244 ~v0 v1 v2 = du__'8799'Gr__1244 v1 v2
du__'8799'Gr__1244 ::
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'Gr__1244 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_act_158
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C_act_158
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.LinCore.Core.C_eff_160
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Core.C_eff_160
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C_act_158
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.LinCore.Core.C_eff_160
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.weakR
d_weakR_1260 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  MAlonzo.Code.Once.LinCore.Core.T_Sg_704 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_weakR_1260 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_weakR_1260
du_weakR_1260 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_weakR_1260
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_map_64
      (coe
         (\ v0 ->
            case coe v0 of
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
                -> coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                     (coe MAlonzo.Code.Once.LinCore.Core.C_there_754 v2)
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.LinCore.ExprBuild.extendR-at
d_extendR'45'at_1284 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_extendR'45'at_1284 ~v0 v1 v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du_extendR'45'at_1284 v1 v2 v4 v5 v6 v7 v8 v9 v10 v11
du_extendR'45'at_1284 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_extendR'45'at_1284 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v6 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
        -> if coe v10
             then coe
                    seq (coe v11)
                    (case coe v7 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                         -> if coe v12
                              then coe
                                     seq (coe v13)
                                     (case coe v8 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                          -> if coe v14
                                               then coe
                                                      seq (coe v15)
                                                      (case coe v9 of
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                           -> if coe v16
                                                                then coe
                                                                       seq (coe v17)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe
                                                                                MAlonzo.Code.Once.LinCore.Core.du_len_734
                                                                                (coe v0))
                                                                             (coe
                                                                                MAlonzo.Code.Once.LinCore.Core.C_here_744)))
                                                                else coe
                                                                       seq (coe v17)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               else coe
                                                      seq (coe v15)
                                                      (coe du_weakR_1260 (coe v1 v2 v3 v4 v5))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              else coe seq (coe v13) (coe du_weakR_1260 (coe v1 v2 v3 v4 v5))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe seq (coe v11) (coe du_weakR_1260 (coe v1 v2 v3 v4 v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.extendR
d_extendR_1366 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_extendR_1366 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_extendR_1366 v1 v2 v3 v4 v5 v6 v7
du_extendR_1366 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_extendR_1366 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_extendR'45'at_1284 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)
      (coe v6)
      (coe
         MAlonzo.Code.Once.CanonicalName.d__'8799''7580'__4
         (coe MAlonzo.Code.Once.CompileSrc.d_csName_1020 (coe v2)) (coe v3))
      (coe
         MAlonzo.Code.Once.IRTy.d__'8799'IRTy__232
         (coe
            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe (0 :: Integer))
            (coe
               du_dcDom_794
               (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v2))))
         (coe v4))
      (coe
         MAlonzo.Code.Once.IRTy.d__'8799'IRTy__232
         (coe
            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe (0 :: Integer))
            (coe
               du_dcCod_796
               (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v2))))
         (coe v5))
      (coe
         du__'8799'Gr__1244
         (coe
            du_dcGr_868
            (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v2)))
         (coe v6))
-- Once.LinCore.ExprBuild.ETProg
d_ETProg_1380 a0 = ()
data T_ETProg_1380
  = C_etProg_1394 MAlonzo.Code.Once.LinCore.Core.T_Cx_728
                  MAlonzo.Code.Once.LinCore.Core.T_Defs_2146
                  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
                   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
                   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
                   MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
                   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Once.LinCore.ExprBuild.ETProg.L
d_L_1388 ::
  T_ETProg_1380 -> MAlonzo.Code.Once.LinCore.Core.T_Cx_728
d_L_1388 v0
  = case coe v0 of
      C_etProg_1394 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.ETProg.defs
d_defs_1390 ::
  T_ETProg_1380 -> MAlonzo.Code.Once.LinCore.Core.T_Defs_2146
d_defs_1390 v0
  = case coe v0 of
      C_etProg_1394 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.ETProg.rs
d_rs_1392 ::
  T_ETProg_1380 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rs_1392 v0
  = case coe v0 of
      C_etProg_1394 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.exprTable
d_exprTable_1396 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] -> T_ETProg_1380
d_exprTable_1396 v0 v1
  = case coe v1 of
      []
        -> coe
             C_etProg_1394 (coe MAlonzo.Code.Once.LinCore.Core.C_ε_730)
             (coe MAlonzo.Code.Once.LinCore.Core.C_ε_2148)
             (coe
                (\ v2 v3 v4 v5 ->
                   coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      (:) v2 v3
        -> coe
             C_etProg_1394
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'9656'__732
                (coe d_L_1388 (coe d_exprTable_1396 (coe v0) (coe v3)))
                (coe d_sgOf_1224 (coe v0) (coe v2)))
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'9656'__2154
                (d_defs_1390 (coe d_exprTable_1396 (coe v0) (coe v3)))
                (d_bodyOf_1234
                   (coe v0) (coe d_L_1388 (coe d_exprTable_1396 (coe v0) (coe v3)))
                   (coe d_rs_1392 (coe d_exprTable_1396 (coe v0) (coe v3))) (coe v2)))
             (coe
                du_extendR_1366
                (coe d_L_1388 (coe d_exprTable_1396 (coe v0) (coe v3)))
                (coe d_rs_1392 (coe d_exprTable_1396 (coe v0) (coe v3))) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.irE
d_irE_1410 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
d_irE_1410 ~v0 v1 = du_irE_1410 v1
du_irE_1410 ::
  MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
du_irE_1410 v0
  = coe
      MAlonzo.Code.Once.Denotation.Program.C_irFun_24
      (coe MAlonzo.Code.Once.CompileSrc.d_csName_1020 (coe v0))
      (coe
         MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe (0 :: Integer))
         (coe
            du_dcDom_794
            (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v0))))
      (coe
         MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe (0 :: Integer))
         (coe
            du_dcCod_796
            (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v0))))
      (coe
         du_dcIR_1060
         (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v0))
         (coe
            MAlonzo.Code.Once.CompileSrc.d_srcIR_42
            (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v0))
            (coe MAlonzo.Code.Once.CompileSrc.d_csSrc_1024 (coe v0))))
-- Once.LinCore.ExprBuild.tblOf
d_tblOf_1414 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_tblOf_1414 ~v0 = du_tblOf_1414
du_tblOf_1414 ::
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
du_tblOf_1414
  = coe MAlonzo.Code.Data.List.Base.du_map_22 (coe du_irE_1410)
-- Once.LinCore.ExprBuild.Graded
d_Graded_1418 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_156 -> ()
d_Graded_1418 = erased
-- Once.LinCore.ExprBuild.GradedRef
d_GradedRef_1438 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_GradedRef_1438 = erased
-- Once.LinCore.ExprBuild.GradedBodies
d_GradedBodies_1538 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] -> ()
d_GradedBodies_1538 = erased
-- Once.LinCore.ExprBuild.SrcsDecl
d_SrcsDecl_1548 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] -> ()
d_SrcsDecl_1548 = erased
-- Once.LinCore.ExprBuild.srcOrder
d_srcOrder_1566 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012]
d_srcOrder_1566 ~v0 v1 v2 = du_srcOrder_1566 v1 v2
du_srcOrder_1566 ::
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012]
du_srcOrder_1566 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             du_srcOrder_1566 (coe v3)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.irFunOf-irE
d_irFunOf'45'irE_1578 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_irFunOf'45'irE_1578 = erased
-- Once.LinCore.ExprBuild.tableOf-go-src
d_tableOf'45'go'45'src_1588 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tableOf'45'go'45'src_1588 = erased
-- Once.LinCore.ExprBuild.tableOf-src
d_tableOf'45'src_1602 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tableOf'45'src_1602 = erased
-- Once.LinCore.ExprBuild.mainCore
d_mainCore_1610 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
d_mainCore_1610 v0 ~v1 v2 v3 v4 = du_mainCore_1610 v0 v2 v3 v4
du_mainCore_1610 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_758
du_mainCore_1610 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'void_14
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
             (coe MAlonzo.Code.Once.LinCore.Core.C_Zero_182)
             (coe MAlonzo.Code.Once.LinCore.Core.C_lzero_904)
             (coe
                MAlonzo.Code.Once.LinCore.FromExpr.du_callM_1824
                (coe MAlonzo.Code.Once.LinCore.Core.C_act_158)
                (coe
                   MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_924 (coe v0)
                   (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
                (coe
                   MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_924 (coe v0)
                   (coe MAlonzo.Code.Once.IRTy.C_Void_18))
                (coe
                   v1
                   (MAlonzo.Code.Once.Spec.Name.d_bare_14
                      (coe ("main" :: Data.Text.Text)))
                   (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                   (coe MAlonzo.Code.Once.IRTy.C_Void_18)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_act_158)))
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'arr_40 v11 v12 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v14 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v17 v18
                      -> case coe v12 of
                           MAlonzo.Code.Once.Spec.Sub.C_sub'45'void_14
                             -> coe
                                  MAlonzo.Code.Once.LinCore.Core.C__'8728'l__796
                                  (coe MAlonzo.Code.Once.LinCore.Core.C_Zero_182)
                                  (coe MAlonzo.Code.Once.LinCore.Core.C_lzero_904)
                                  (coe
                                     MAlonzo.Code.Once.LinCore.FromExpr.du_callM_1824
                                     (coe MAlonzo.Code.Once.LinCore.FromIR.du_grade_922 (coe v18))
                                     (coe
                                        MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_924
                                        (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
                                     (coe
                                        MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_924
                                        (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Void_18))
                                     (coe
                                        v1
                                        (MAlonzo.Code.Once.Spec.Name.d_bare_14
                                           (coe ("main" :: Data.Text.Text)))
                                        (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                                        (coe MAlonzo.Code.Once.IRTy.C_Void_18)
                                        (coe
                                           MAlonzo.Code.Once.LinCore.FromIR.du_grade_922
                                           (coe v18))))
                           MAlonzo.Code.Once.Spec.Sub.C_sub'45'unit_20
                             -> coe
                                  MAlonzo.Code.Once.LinCore.FromExpr.du_callM_1824
                                  (coe MAlonzo.Code.Once.LinCore.FromIR.du_grade_922 (coe v18))
                                  (coe
                                     MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_924 (coe v0)
                                     (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
                                  (coe
                                     MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_924 (coe v0)
                                     (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
                                  (coe
                                     v1
                                     (MAlonzo.Code.Once.Spec.Name.d_bare_14
                                        (coe ("main" :: Data.Text.Text)))
                                     (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                                     (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                                     (coe MAlonzo.Code.Once.LinCore.FromIR.du_grade_922 (coe v18)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.MainGraded
d_MainGraded_1634 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_728 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.LinCore.Core.T_Gr_156 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 -> ()
d_MainGraded_1634 = erased
-- Once.LinCore.ExprBuild.Bridged
d_Bridged_1660 a0 a1 a2 a3 = ()
data T_Bridged_1660
  = C_constructor_1700 [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012]
                       AgdaAny AgdaAny MAlonzo.Code.Once.Spec.Type.T_Ty_8
                       MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8
-- Once.LinCore.ExprBuild.Bridged.tl
d_tl_1684 ::
  T_Bridged_1660 -> [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012]
d_tl_1684 v0
  = case coe v0 of
      C_constructor_1700 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.Bridged.gb
d_gb_1686 :: T_Bridged_1660 -> AgdaAny
d_gb_1686 v0
  = case coe v0 of
      C_constructor_1700 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.Bridged.sd
d_sd_1688 :: T_Bridged_1660 -> AgdaAny
d_sd_1688 v0
  = case coe v0 of
      C_constructor_1700 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.Bridged.mty
d_mty_1690 :: T_Bridged_1660 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_mty_1690 v0
  = case coe v0 of
      C_constructor_1700 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.Bridged.mpm
d_mpm_1692 ::
  T_Bridged_1660 -> MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8
d_mpm_1692 v0
  = case coe v0 of
      C_constructor_1700 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.Bridged.mg
d_mg_1694 :: T_Bridged_1660 -> AgdaAny
d_mg_1694 = erased
-- Once.LinCore.ExprBuild.Bridged.tbl-eq
d_tbl'45'eq_1696 ::
  T_Bridged_1660 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tbl'45'eq_1696 = erased
-- Once.LinCore.ExprBuild.Bridged.mir
d_mir_1698 ::
  T_Bridged_1660 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mir_1698 = erased
