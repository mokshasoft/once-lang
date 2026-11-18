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
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_152 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754 -> ()
d_Gd_50 = erased
-- Once.LinCore.ExprBuild._.Gr
d_Gr_52 a0 = ()
-- Once.LinCore.ExprBuild._.Kd
d_Kd_58 a0 = ()
-- Once.LinCore.ExprBuild._.LTm
d_LTm_70 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 -> ()
d_LTm_70 = erased
-- Once.LinCore.ExprBuild._.LTy
d_LTy_72 a0 = ()
-- Once.LinCore.ExprBuild._.Sg
d_Sg_88 a0 = ()
-- Once.LinCore.ExprBuild._.Tm
d_Tm_96 a0 a1 a2 a3 a4 = ()
-- Once.LinCore.ExprBuild._.Sg.cod
d_cod_530 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_700 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174
d_cod_530 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_cod_720 (coe v0)
-- Once.LinCore.ExprBuild._.Sg.dom
d_dom_532 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_700 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174
d_dom_532 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_dom_718 (coe v0)
-- Once.LinCore.ExprBuild._.Sg.env
d_env_534 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_700 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174
d_env_534 v0
  = coe MAlonzo.Code.Once.LinCore.Core.d_env_716 (coe v0)
-- Once.LinCore.ExprBuild._.Sg.gr
d_gr_536 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_700 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_152
d_gr_536 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_gr_714 (coe v0)
-- Once.LinCore.ExprBuild._.Sg.kd
d_kd_538 ::
  MAlonzo.Code.Once.LinCore.Core.T_Sg_700 ->
  MAlonzo.Code.Once.LinCore.Core.T_Kd_146
d_kd_538 v0 = coe MAlonzo.Code.Once.LinCore.Core.d_kd_712 (coe v0)
-- Once.LinCore.ExprBuild._.Co
d_Co_742 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174
d_Co_742 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.LinCore.FromExpr.du_Co_774 (coe v0) v1 v3 v4
-- Once.LinCore.ExprBuild._.ty
d_ty_754 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174
d_ty_754 v0
  = coe MAlonzo.Code.Once.LinCore.FromExpr.d_ty_766 (coe v0)
-- Once.LinCore.ExprBuild._.grade
d_grade_758 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_152
d_grade_758 ~v0 = du_grade_758
du_grade_758 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_152
du_grade_758 = coe MAlonzo.Code.Once.LinCore.FromIR.du_grade_968
-- Once.LinCore.ExprBuild._.⟪_⟫
d_'10218'_'10219'_762 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174
d_'10218'_'10219'_762 v0
  = coe
      MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_970 (coe v0)
-- Once.LinCore.ExprBuild._.Rs
d_Rs_770 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 -> ()
d_Rs_770 = erased
-- Once.LinCore.ExprBuild._.eraseL
d_eraseL_792 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754
d_eraseL_792 v0 ~v1 ~v2 v3 ~v4 v5 v6 = du_eraseL_792 v0 v3 v5 v6
du_eraseL_792 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754
du_eraseL_792 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Spec.Context.C_'8709'_12
        -> coe seq (coe v3) (coe MAlonzo.Code.Once.LinCore.Core.C_lid_782)
      MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v5 v6
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v8 v9
               -> case coe v8 of
                    MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                           (MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_970
                              (coe v0)
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe v1)
                                 (coe
                                    MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                    (coe v5))))
                           (coe du_eraseL_792 (coe v0) (coe v1) (coe v5) (coe v9))
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855't__180
                                 (coe
                                    MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_970 (coe v0)
                                    (coe
                                       MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe v1)
                                       (coe
                                          MAlonzo.Code.Once.Context.du_'10214'_'10215''7580'_14
                                          (coe v5))))
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_One_176))
                              (coe MAlonzo.Code.Once.LinCore.Core.C_ρl_810)
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855'l__804
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_lid_782)
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_drop_868)))
                    MAlonzo.Code.Once.Spec.Grade.C_One_10
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C__'8855'l__804
                           (coe du_eraseL_792 (coe v0) (coe v1) (coe v5) (coe v9))
                           (coe MAlonzo.Code.Once.LinCore.Core.C_lid_782)
                    MAlonzo.Code.Once.Spec.Grade.C_Many_12
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C__'8855'l__804
                           (coe du_eraseL_792 (coe v0) (coe v1) (coe v5) (coe v9))
                           (coe MAlonzo.Code.Once.LinCore.Core.C_lid_782)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild._.k-eraseL
d_k'45'eraseL_820 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_764
d_k'45'eraseL_820 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_k'45'eraseL_820 v5 v6
du_k'45'eraseL_820 ::
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_764
du_k'45'eraseL_820 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'8709'_12
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1114)
      MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v6 v7
               -> case coe v6 of
                    MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
                           (coe du_k'45'eraseL_820 (coe v3) (coe v7))
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
                              (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'ρ_1150)
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1144
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1114)
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'drop_1208)))
                    MAlonzo.Code.Once.Spec.Grade.C_One_10
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1144
                           (coe du_k'45'eraseL_820 (coe v3) (coe v7))
                           (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1114)
                    MAlonzo.Code.Once.Spec.Grade.C_Many_12
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1144
                           (coe du_k'45'eraseL_820 (coe v3) (coe v7))
                           (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1114)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.dcDom
d_dcDom_840 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_dcDom_840 ~v0 v1 = du_dcDom_840 v1
du_dcDom_840 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
du_dcDom_840 v0
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
d_dcCod_842 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_dcCod_842 ~v0 v1 = du_dcCod_842 v1
du_dcCod_842 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8
du_dcCod_842 v0
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
d_dcGr_914 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_152
d_dcGr_914 ~v0 v1 = du_dcGr_914 v1
du_dcGr_914 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_152
du_dcGr_914 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe MAlonzo.Code.Once.LinCore.Core.C_act_154
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe MAlonzo.Code.Once.LinCore.Core.C_act_154
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v1 v2
        -> coe MAlonzo.Code.Once.LinCore.Core.C_act_154
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v1 v2
        -> coe MAlonzo.Code.Once.LinCore.Core.C_act_154
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v1 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v4 v5
               -> coe MAlonzo.Code.Once.LinCore.FromIR.du_grade_968 (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v1
        -> coe MAlonzo.Code.Once.LinCore.Core.C_act_154
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v1 v2
        -> coe MAlonzo.Code.Once.LinCore.Core.C_act_154
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe MAlonzo.Code.Once.LinCore.Core.C_act_154
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe MAlonzo.Code.Once.LinCore.Core.C_act_154
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild._.dc
d_dc_946 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754
d_dc_946 v0 ~v1 v2 v3 = du_dc_946 v0 v2 v3
du_dc_946 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754
du_dc_946 v0 v1 v2
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
                           MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C__'8855't__180
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C_Fn_186
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_many_150)
                                 (coe MAlonzo.Code.Once.LinCore.FromIR.du_grade_968 (coe v7))
                                 (coe
                                    MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_970 (coe v0)
                                    (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
                                 (coe
                                    MAlonzo.Code.Once.LinCore.FromExpr.d_ty_766 (coe v0)
                                    (coe (0 :: Integer)) (coe du_dcCod_842 (coe v1))))
                              (coe
                                 MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_970 (coe v0)
                                 (coe MAlonzo.Code.Once.IRTy.C_Unit_16)))
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855't__180
                                 (coe
                                    MAlonzo.Code.Once.LinCore.Core.C_Fn_186
                                    (coe MAlonzo.Code.Once.LinCore.Core.C_many_150)
                                    (coe MAlonzo.Code.Once.LinCore.FromIR.du_grade_968 (coe v7))
                                    (coe
                                       MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_970
                                       (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
                                    (coe
                                       MAlonzo.Code.Once.LinCore.FromExpr.d_ty_766 (coe v0)
                                       (coe (0 :: Integer)) (coe du_dcCod_842 (coe v1))))
                                 (coe
                                    MAlonzo.Code.Once.LinCore.FromExpr.d_ty_766 (coe v0)
                                    (coe (0 :: Integer)) (coe du_dcCod_842 (coe v1))))
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                                 (coe
                                    MAlonzo.Code.Once.LinCore.Core.C__'8855't__180
                                    (coe MAlonzo.Code.Once.LinCore.Core.C_One_176)
                                    (coe
                                       MAlonzo.Code.Once.LinCore.FromExpr.d_ty_766 (coe v0)
                                       (coe (0 :: Integer)) (coe du_dcCod_842 (coe v1))))
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_lul_822)
                                 (coe
                                    MAlonzo.Code.Once.LinCore.Core.C__'8855'l__804
                                    (coe MAlonzo.Code.Once.LinCore.Core.C_drop_868)
                                    (coe MAlonzo.Code.Once.LinCore.Core.C_lid_782)))
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C_lend_962
                                 (coe
                                    MAlonzo.Code.Once.LinCore.Core.C_bsnd_990
                                    (coe MAlonzo.Code.Once.LinCore.Core.C_bev_1070))))
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855't__180
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_One_176)
                                 (coe
                                    MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_970 (coe v0)
                                    (coe MAlonzo.Code.Once.IRTy.C_Unit_16)))
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855'l__804 v2
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_lid_782))
                              (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_828))
                    MAlonzo.Code.Once.Spec.Grade.C_One_10
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C__'8855't__180
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C_Fn_186
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_many_150)
                                 (coe MAlonzo.Code.Once.LinCore.FromIR.du_grade_968 (coe v7))
                                 (coe
                                    MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_970 (coe v0)
                                    (coe
                                       MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                       (coe (0 :: Integer)) (coe v3)))
                                 (coe
                                    MAlonzo.Code.Once.LinCore.FromExpr.d_ty_766 (coe v0)
                                    (coe (0 :: Integer)) (coe du_dcCod_842 (coe v1))))
                              (coe
                                 MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_970 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe (0 :: Integer))
                                    (coe v3))))
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855't__180
                                 (coe
                                    MAlonzo.Code.Once.LinCore.Core.C_Fn_186
                                    (coe MAlonzo.Code.Once.LinCore.Core.C_many_150)
                                    (coe MAlonzo.Code.Once.LinCore.FromIR.du_grade_968 (coe v7))
                                    (coe
                                       MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_970
                                       (coe v0)
                                       (coe
                                          MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                          (coe (0 :: Integer)) (coe v3)))
                                    (coe
                                       MAlonzo.Code.Once.LinCore.FromExpr.d_ty_766 (coe v0)
                                       (coe (0 :: Integer)) (coe du_dcCod_842 (coe v1))))
                                 (coe
                                    MAlonzo.Code.Once.LinCore.FromExpr.d_ty_766 (coe v0)
                                    (coe (0 :: Integer)) (coe du_dcCod_842 (coe v1))))
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                                 (coe
                                    MAlonzo.Code.Once.LinCore.Core.C__'8855't__180
                                    (coe MAlonzo.Code.Once.LinCore.Core.C_One_176)
                                    (coe
                                       MAlonzo.Code.Once.LinCore.FromExpr.d_ty_766 (coe v0)
                                       (coe (0 :: Integer)) (coe du_dcCod_842 (coe v1))))
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_lul_822)
                                 (coe
                                    MAlonzo.Code.Once.LinCore.Core.C__'8855'l__804
                                    (coe MAlonzo.Code.Once.LinCore.Core.C_drop_868)
                                    (coe MAlonzo.Code.Once.LinCore.Core.C_lid_782)))
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C_lend_962
                                 (coe
                                    MAlonzo.Code.Once.LinCore.Core.C_bsnd_990
                                    (coe MAlonzo.Code.Once.LinCore.Core.C_bev_1070))))
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855't__180
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_One_176)
                                 (coe
                                    MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_970 (coe v0)
                                    (coe
                                       MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                       (coe (0 :: Integer)) (coe v3))))
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855'l__804 v2
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_lid_782))
                              (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_828))
                    MAlonzo.Code.Once.Spec.Grade.C_Many_12
                      -> coe
                           MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C__'8855't__180
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C_Fn_186
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_many_150)
                                 (coe MAlonzo.Code.Once.LinCore.FromIR.du_grade_968 (coe v7))
                                 (coe
                                    MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_970 (coe v0)
                                    (coe
                                       MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                       (coe (0 :: Integer)) (coe v3)))
                                 (coe
                                    MAlonzo.Code.Once.LinCore.FromExpr.d_ty_766 (coe v0)
                                    (coe (0 :: Integer)) (coe du_dcCod_842 (coe v1))))
                              (coe
                                 MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_970 (coe v0)
                                 (coe
                                    MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe (0 :: Integer))
                                    (coe v3))))
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855't__180
                                 (coe
                                    MAlonzo.Code.Once.LinCore.Core.C_Fn_186
                                    (coe MAlonzo.Code.Once.LinCore.Core.C_many_150)
                                    (coe MAlonzo.Code.Once.LinCore.FromIR.du_grade_968 (coe v7))
                                    (coe
                                       MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_970
                                       (coe v0)
                                       (coe
                                          MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                          (coe (0 :: Integer)) (coe v3)))
                                    (coe
                                       MAlonzo.Code.Once.LinCore.FromExpr.d_ty_766 (coe v0)
                                       (coe (0 :: Integer)) (coe du_dcCod_842 (coe v1))))
                                 (coe
                                    MAlonzo.Code.Once.LinCore.FromExpr.d_ty_766 (coe v0)
                                    (coe (0 :: Integer)) (coe du_dcCod_842 (coe v1))))
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                                 (coe
                                    MAlonzo.Code.Once.LinCore.Core.C__'8855't__180
                                    (coe MAlonzo.Code.Once.LinCore.Core.C_One_176)
                                    (coe
                                       MAlonzo.Code.Once.LinCore.FromExpr.d_ty_766 (coe v0)
                                       (coe (0 :: Integer)) (coe du_dcCod_842 (coe v1))))
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_lul_822)
                                 (coe
                                    MAlonzo.Code.Once.LinCore.Core.C__'8855'l__804
                                    (coe MAlonzo.Code.Once.LinCore.Core.C_drop_868)
                                    (coe MAlonzo.Code.Once.LinCore.Core.C_lid_782)))
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C_lend_962
                                 (coe
                                    MAlonzo.Code.Once.LinCore.Core.C_bsnd_990
                                    (coe MAlonzo.Code.Once.LinCore.Core.C_bev_1070))))
                           (coe
                              MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855't__180
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_One_176)
                                 (coe
                                    MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_970 (coe v0)
                                    (coe
                                       MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56
                                       (coe (0 :: Integer)) (coe v3))))
                              (coe
                                 MAlonzo.Code.Once.LinCore.Core.C__'8855'l__804 v2
                                 (coe MAlonzo.Code.Once.LinCore.Core.C_lid_782))
                              (coe MAlonzo.Code.Once.LinCore.Core.C_lul'8315'_828))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v3 -> coe v2
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v3 v4 -> coe v2
      MAlonzo.Code.Once.Spec.Type.C_Int_32 -> coe v2
      MAlonzo.Code.Once.Spec.Type.C_Float_34 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild._.gdT
d_gdT_1014 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754 ->
  (MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.LinCore.Core.T_Blk_764) ->
  AgdaAny
d_gdT_1014 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 = du_gdT_1014 v4 v6
du_gdT_1014 ::
  MAlonzo.Code.Once.Spec.Grade.T_Purity_40 ->
  (MAlonzo.Code.Once.Spec.Grade.T_Finite_34 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Once.LinCore.Core.T_Blk_764) ->
  AgdaAny
du_gdT_1014 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_fin_42 v2 -> coe v1 v2 erased
      MAlonzo.Code.Once.Spec.Grade.C_eff_44
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild._.dcGd
d_dcGd_1030 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_764 -> AgdaAny
d_dcGd_1030 ~v0 ~v1 v2 ~v3 v4 = du_dcGd_1030 v2 v4
du_dcGd_1030 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_764 -> AgdaAny
du_dcGd_1030 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Type.C_Unit_18
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128 v1
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1162)
      MAlonzo.Code.Once.Spec.Type.C_Void_20
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128 v1
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1162)
      MAlonzo.Code.Once.Spec.Type.C__'42'__22 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128 v1
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1162)
      MAlonzo.Code.Once.Spec.Type.C__'43'__24 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128 v1
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1162)
      MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v2 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v5 v6
               -> coe
                    seq (coe v5)
                    (coe
                       du_gdT_1014 (coe v6)
                       (coe
                          (\ v7 v8 ->
                             coe
                               MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
                               (coe
                                  MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
                                  (coe
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
                                           (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'bev_1432))))
                                  (coe
                                     MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
                                     (coe
                                        MAlonzo.Code.Once.LinCore.Core.C_k'45''8855'_1144 v1
                                        (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'id_1114))
                                     (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul'8315'_1168)))
                               (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1162))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Spec.Type.C_μ_28 v2
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128 v1
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1162)
      MAlonzo.Code.Once.Spec.Type.C_ν_30 v2 v3
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128 v1
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1162)
      MAlonzo.Code.Once.Spec.Type.C_Int_32
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128 v1
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1162)
      MAlonzo.Code.Once.Spec.Type.C_Float_34
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128 v1
             (coe MAlonzo.Code.Once.LinCore.Core.C_k'45'lul_1162)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.dcIR
d_dcIR_1106 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
d_dcIR_1106 ~v0 v1 v2 = du_dcIR_1106 v1 v2
du_dcIR_1106 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> MAlonzo.Code.Once.IR.T_IR_16
du_dcIR_1106 v0 v1
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
                                    (coe du_dcCod_842 (coe v0))))
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
                                    (coe du_dcCod_842 (coe v0))))
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
                                    (coe du_dcCod_842 (coe v0))))
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
d_dc'45'eq_1168 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_dc'45'eq_1168 = erased
-- Once.LinCore.ExprBuild.val
d_val_1230 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.LinCore.Core.T_Gr_152 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.CompileSrc.T_Src_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754
d_val_1230 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Once.CompileSrc.C_src_38 v5 v6 v7 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
             (coe
                MAlonzo.Code.Once.LinCore.FromExpr.du_Co_774 (coe v0)
                (coe (0 :: Integer)) (coe v6) (coe v7))
             (MAlonzo.Code.Once.LinCore.FromExpr.d_Lq_2084
                (coe v0) (coe v1) (coe v3) (coe (0 :: Integer)) (coe v5) (coe v6)
                (coe v7) (coe v2) (coe v11))
             (coe du_eraseL_792 (coe v0) (coe (0 :: Integer)) (coe v6) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.k-val
d_k'45'val_1254 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.LinCore.Core.T_Gr_152 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.CompileSrc.T_Src_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_764
d_k'45'val_1254 ~v0 ~v1 v2 v3 v4 = du_k'45'val_1254 v2 v3 v4
du_k'45'val_1254 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.LinCore.Core.T_Gr_152 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.CompileSrc.T_Src_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Blk_764
du_k'45'val_1254 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.CompileSrc.C_src_38 v3 v4 v5 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C_k'45''8728'_1128
             (coe
                MAlonzo.Code.Once.LinCore.FromExpr.du_Lq'45'blk_2098 (coe v1)
                (coe (0 :: Integer)) (coe v3) (coe v4) (coe v0) (coe v9))
             (coe du_k'45'eraseL_820 (coe v4) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.sgOf
d_sgOf_1270 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012 ->
  MAlonzo.Code.Once.LinCore.Core.T_Sg_700
d_sgOf_1270 v0 v1
  = coe
      MAlonzo.Code.Once.LinCore.Core.C_sg_722
      (coe MAlonzo.Code.Once.LinCore.Core.C_once_148)
      (coe
         du_dcGr_914
         (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v1)))
      (coe MAlonzo.Code.Once.LinCore.Core.C_One_176)
      (coe
         MAlonzo.Code.Once.LinCore.FromExpr.d_ty_766 (coe v0)
         (coe (0 :: Integer))
         (coe
            du_dcDom_840
            (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v1))))
      (coe
         MAlonzo.Code.Once.LinCore.FromExpr.d_ty_766 (coe v0)
         (coe (0 :: Integer))
         (coe
            du_dcCod_842
            (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v1))))
-- Once.LinCore.ExprBuild.bodyOf
d_bodyOf_1280 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.LinCore.Core.T_Gr_152 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012 ->
  MAlonzo.Code.Once.LinCore.Core.T_Body_1650
d_bodyOf_1280 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.LinCore.Core.C_b1_1664
      (coe
         MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
         (MAlonzo.Code.Once.LinCore.FromExpr.d_ty_766
            (coe v0) (coe (0 :: Integer))
            (coe
               du_dcDom_840
               (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v3))))
         (coe
            du_dc_946 (coe v0)
            (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v3))
            (coe
               d_val_1230 (coe v0) (coe v1)
               (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v3)) (coe v2)
               (coe MAlonzo.Code.Once.CompileSrc.d_csSrc_1024 (coe v3))))
         (coe MAlonzo.Code.Once.LinCore.Core.C_lul_822))
      (coe
         du_dcGd_1030
         (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v3))
         (coe
            du_k'45'val_1254
            (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v3)) (coe v2)
            (coe MAlonzo.Code.Once.CompileSrc.d_csSrc_1024 (coe v3))))
-- Once.LinCore.ExprBuild._≟Gr_
d__'8799'Gr__1290 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_152 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_152 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'Gr__1290 ~v0 v1 v2 = du__'8799'Gr__1290 v1 v2
du__'8799'Gr__1290 ::
  MAlonzo.Code.Once.LinCore.Core.T_Gr_152 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_152 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'Gr__1290 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_act_154
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C_act_154
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             MAlonzo.Code.Once.LinCore.Core.C_eff_156
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Core.C_eff_156
        -> case coe v1 of
             MAlonzo.Code.Once.LinCore.Core.C_act_154
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Once.LinCore.Core.C_eff_156
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.weakR
d_weakR_1306 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  MAlonzo.Code.Once.LinCore.Core.T_Sg_700 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_152 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_weakR_1306 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_weakR_1306
du_weakR_1306 ::
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_weakR_1306
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_map_64
      (coe
         (\ v0 ->
            case coe v0 of
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
                -> coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                     (coe MAlonzo.Code.Once.LinCore.Core.C_there_750 v2)
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Once.LinCore.ExprBuild.extendR-at
d_extendR'45'at_1330 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.LinCore.Core.T_Gr_152 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_152 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_extendR'45'at_1330 ~v0 v1 v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du_extendR'45'at_1330 v1 v2 v4 v5 v6 v7 v8 v9 v10 v11
du_extendR'45'at_1330 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.LinCore.Core.T_Gr_152 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_152 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_extendR'45'at_1330 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
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
                                                                                MAlonzo.Code.Once.LinCore.Core.du_len_730
                                                                                (coe v0))
                                                                             (coe
                                                                                MAlonzo.Code.Once.LinCore.Core.C_here_740)))
                                                                else coe
                                                                       seq (coe v17)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               else coe
                                                      seq (coe v15)
                                                      (coe du_weakR_1306 (coe v1 v2 v3 v4 v5))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              else coe seq (coe v13) (coe du_weakR_1306 (coe v1 v2 v3 v4 v5))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             else coe seq (coe v11) (coe du_weakR_1306 (coe v1 v2 v3 v4 v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.extendR
d_extendR_1412 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.LinCore.Core.T_Gr_152 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_152 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_extendR_1412 ~v0 v1 v2 v3 v4 v5 v6 v7
  = du_extendR_1412 v1 v2 v3 v4 v5 v6 v7
du_extendR_1412 ::
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.LinCore.Core.T_Gr_152 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_152 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_extendR_1412 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_extendR'45'at_1330 (coe v0) (coe v1) (coe v3) (coe v4) (coe v5)
      (coe v6)
      (coe
         MAlonzo.Code.Once.CanonicalName.d__'8799''7580'__4
         (coe MAlonzo.Code.Once.CompileSrc.d_csName_1020 (coe v2)) (coe v3))
      (coe
         MAlonzo.Code.Once.IRTy.d__'8799'IRTy__206
         (coe
            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe (0 :: Integer))
            (coe
               du_dcDom_840
               (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v2))))
         (coe v4))
      (coe
         MAlonzo.Code.Once.IRTy.d__'8799'IRTy__206
         (coe
            MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe (0 :: Integer))
            (coe
               du_dcCod_842
               (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v2))))
         (coe v5))
      (coe
         du__'8799'Gr__1290
         (coe
            du_dcGr_914
            (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v2)))
         (coe v6))
-- Once.LinCore.ExprBuild.ETProg
d_ETProg_1426 a0 = ()
data T_ETProg_1426
  = C_etProg_1440 MAlonzo.Code.Once.LinCore.Core.T_Cx_724
                  MAlonzo.Code.Once.LinCore.Core.T_Defs_1678
                  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
                   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
                   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
                   MAlonzo.Code.Once.LinCore.Core.T_Gr_152 ->
                   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Once.LinCore.ExprBuild.ETProg.L
d_L_1434 ::
  T_ETProg_1426 -> MAlonzo.Code.Once.LinCore.Core.T_Cx_724
d_L_1434 v0
  = case coe v0 of
      C_etProg_1440 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.ETProg.defs
d_defs_1436 ::
  T_ETProg_1426 -> MAlonzo.Code.Once.LinCore.Core.T_Defs_1678
d_defs_1436 v0
  = case coe v0 of
      C_etProg_1440 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.ETProg.rs
d_rs_1438 ::
  T_ETProg_1426 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_152 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rs_1438 v0
  = case coe v0 of
      C_etProg_1440 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.exprTable
d_exprTable_1442 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] -> T_ETProg_1426
d_exprTable_1442 v0 v1
  = case coe v1 of
      []
        -> coe
             C_etProg_1440 (coe MAlonzo.Code.Once.LinCore.Core.C_ε_726)
             (coe MAlonzo.Code.Once.LinCore.Core.C_ε_1680)
             (coe
                (\ v2 v3 v4 v5 ->
                   coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      (:) v2 v3
        -> coe
             C_etProg_1440
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'9656'__728
                (coe d_L_1434 (coe d_exprTable_1442 (coe v0) (coe v3)))
                (coe d_sgOf_1270 (coe v0) (coe v2)))
             (coe
                MAlonzo.Code.Once.LinCore.Core.C__'9656'__1686
                (d_defs_1436 (coe d_exprTable_1442 (coe v0) (coe v3)))
                (d_bodyOf_1280
                   (coe v0) (coe d_L_1434 (coe d_exprTable_1442 (coe v0) (coe v3)))
                   (coe d_rs_1438 (coe d_exprTable_1442 (coe v0) (coe v3))) (coe v2)))
             (coe
                du_extendR_1412
                (coe d_L_1434 (coe d_exprTable_1442 (coe v0) (coe v3)))
                (coe d_rs_1438 (coe d_exprTable_1442 (coe v0) (coe v3))) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.irE
d_irE_1456 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
d_irE_1456 ~v0 v1 = du_irE_1456 v1
du_irE_1456 ::
  MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012 ->
  MAlonzo.Code.Once.Denotation.Program.T_IRFun_6
du_irE_1456 v0
  = coe
      MAlonzo.Code.Once.Denotation.Program.C_irFun_24
      (coe MAlonzo.Code.Once.CompileSrc.d_csName_1020 (coe v0))
      (coe
         MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe (0 :: Integer))
         (coe
            du_dcDom_840
            (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v0))))
      (coe
         MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_56 (coe (0 :: Integer))
         (coe
            du_dcCod_842
            (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v0))))
      (coe
         du_dcIR_1106
         (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v0))
         (coe
            MAlonzo.Code.Once.CompileSrc.d_srcIR_42
            (coe MAlonzo.Code.Once.CompileSrc.d_csType_1022 (coe v0))
            (coe MAlonzo.Code.Once.CompileSrc.d_csSrc_1024 (coe v0))))
-- Once.LinCore.ExprBuild.tblOf
d_tblOf_1460 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
d_tblOf_1460 ~v0 = du_tblOf_1460
du_tblOf_1460 ::
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  [MAlonzo.Code.Once.Denotation.Program.T_IRFun_6]
du_tblOf_1460
  = coe MAlonzo.Code.Data.List.Base.du_map_22 (coe du_irE_1456)
-- Once.LinCore.ExprBuild.Graded
d_Graded_1464 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.LinCore.Core.T_Gr_152 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Gr_152 -> ()
d_Graded_1464 = erased
-- Once.LinCore.ExprBuild.GradedRef
d_GradedRef_1484 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.LinCore.Core.T_Gr_152 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 -> ()
d_GradedRef_1484 = erased
-- Once.LinCore.ExprBuild.GradedBodies
d_GradedBodies_1584 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] -> ()
d_GradedBodies_1584 = erased
-- Once.LinCore.ExprBuild.SrcsDecl
d_SrcsDecl_1594 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] -> ()
d_SrcsDecl_1594 = erased
-- Once.LinCore.ExprBuild.srcOrder
d_srcOrder_1612 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012]
d_srcOrder_1612 ~v0 v1 v2 = du_srcOrder_1612 v1 v2
du_srcOrder_1612 ::
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012]
du_srcOrder_1612 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             du_srcOrder_1612 (coe v3)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.irFunOf-irE
d_irFunOf'45'irE_1624 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_irFunOf'45'irE_1624 = erased
-- Once.LinCore.ExprBuild.tableOf-go-src
d_tableOf'45'go'45'src_1634 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tableOf'45'go'45'src_1634 = erased
-- Once.LinCore.ExprBuild.tableOf-src
d_tableOf'45'src_1648 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tableOf'45'src_1648 = erased
-- Once.LinCore.ExprBuild.mainCore
d_mainCore_1656 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.LinCore.Core.T_Gr_152 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754
d_mainCore_1656 v0 ~v1 v2 v3 v4 = du_mainCore_1656 v0 v2 v3 v4
du_mainCore_1656 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.LinCore.Core.T_Gr_152 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 ->
  MAlonzo.Code.Once.LinCore.Core.T_Tm_754
du_mainCore_1656 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'void_14
        -> coe
             MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
             (coe MAlonzo.Code.Once.LinCore.Core.C_Zero_178)
             (coe MAlonzo.Code.Once.LinCore.Core.C_lzero_900)
             (coe
                MAlonzo.Code.Once.LinCore.FromExpr.du_callM_1860
                (coe MAlonzo.Code.Once.LinCore.Core.C_act_154)
                (coe
                   MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_970 (coe v0)
                   (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
                (coe
                   MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_970 (coe v0)
                   (coe MAlonzo.Code.Once.IRTy.C_Void_18))
                (coe
                   v1
                   (MAlonzo.Code.Once.Spec.Name.d_bare_14
                      (coe ("main" :: Data.Text.Text)))
                   (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                   (coe MAlonzo.Code.Once.IRTy.C_Void_18)
                   (coe MAlonzo.Code.Once.LinCore.Core.C_act_154)))
      MAlonzo.Code.Once.Spec.Sub.C_sub'45'arr_40 v11 v12 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v14 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v17 v18
                      -> case coe v12 of
                           MAlonzo.Code.Once.Spec.Sub.C_sub'45'void_14
                             -> coe
                                  MAlonzo.Code.Once.LinCore.Core.C__'8728'l__792
                                  (coe MAlonzo.Code.Once.LinCore.Core.C_Zero_178)
                                  (coe MAlonzo.Code.Once.LinCore.Core.C_lzero_900)
                                  (coe
                                     MAlonzo.Code.Once.LinCore.FromExpr.du_callM_1860
                                     (coe MAlonzo.Code.Once.LinCore.FromIR.du_grade_968 (coe v18))
                                     (coe
                                        MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_970
                                        (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
                                     (coe
                                        MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_970
                                        (coe v0) (coe MAlonzo.Code.Once.IRTy.C_Void_18))
                                     (coe
                                        v1
                                        (MAlonzo.Code.Once.Spec.Name.d_bare_14
                                           (coe ("main" :: Data.Text.Text)))
                                        (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                                        (coe MAlonzo.Code.Once.IRTy.C_Void_18)
                                        (coe
                                           MAlonzo.Code.Once.LinCore.FromIR.du_grade_968
                                           (coe v18))))
                           MAlonzo.Code.Once.Spec.Sub.C_sub'45'unit_20
                             -> coe
                                  MAlonzo.Code.Once.LinCore.FromExpr.du_callM_1860
                                  (coe MAlonzo.Code.Once.LinCore.FromIR.du_grade_968 (coe v18))
                                  (coe
                                     MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_970 (coe v0)
                                     (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
                                  (coe
                                     MAlonzo.Code.Once.LinCore.FromIR.d_'10218'_'10219'_970 (coe v0)
                                     (coe MAlonzo.Code.Once.IRTy.C_Unit_16))
                                  (coe
                                     v1
                                     (MAlonzo.Code.Once.Spec.Name.d_bare_14
                                        (coe ("main" :: Data.Text.Text)))
                                     (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                                     (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
                                     (coe MAlonzo.Code.Once.LinCore.FromIR.du_grade_968 (coe v18)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.MainGraded
d_MainGraded_1680 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_Cx_724 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
   MAlonzo.Code.Once.LinCore.Core.T_Gr_152 ->
   Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8 -> ()
d_MainGraded_1680 = erased
-- Once.LinCore.ExprBuild.Bridged
d_Bridged_1706 a0 a1 a2 a3 = ()
data T_Bridged_1706
  = C_constructor_1746 [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012]
                       AgdaAny AgdaAny MAlonzo.Code.Once.Spec.Type.T_Ty_8
                       MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8
-- Once.LinCore.ExprBuild.Bridged.tl
d_tl_1730 ::
  T_Bridged_1706 -> [MAlonzo.Code.Once.CompileSrc.T_CompiledSrc_1012]
d_tl_1730 v0
  = case coe v0 of
      C_constructor_1746 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.Bridged.gb
d_gb_1732 :: T_Bridged_1706 -> AgdaAny
d_gb_1732 v0
  = case coe v0 of
      C_constructor_1746 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.Bridged.sd
d_sd_1734 :: T_Bridged_1706 -> AgdaAny
d_sd_1734 v0
  = case coe v0 of
      C_constructor_1746 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.Bridged.mty
d_mty_1736 :: T_Bridged_1706 -> MAlonzo.Code.Once.Spec.Type.T_Ty_8
d_mty_1736 v0
  = case coe v0 of
      C_constructor_1746 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.Bridged.mpm
d_mpm_1738 ::
  T_Bridged_1706 -> MAlonzo.Code.Once.Spec.Sub.T__'60''58'__8
d_mpm_1738 v0
  = case coe v0 of
      C_constructor_1746 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.ExprBuild.Bridged.mg
d_mg_1740 :: T_Bridged_1706 -> AgdaAny
d_mg_1740 = erased
-- Once.LinCore.ExprBuild.Bridged.tbl-eq
d_tbl'45'eq_1742 ::
  T_Bridged_1706 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tbl'45'eq_1742 = erased
-- Once.LinCore.ExprBuild.Bridged.mir
d_mir_1744 ::
  T_Bridged_1706 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mir_1744 = erased
