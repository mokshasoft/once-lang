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

module MAlonzo.Code.Once.LinCore.Linear where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Once.Context
import qualified MAlonzo.Code.Once.LinCore.CopyFree
import qualified MAlonzo.Code.Once.LinCore.Core
import qualified MAlonzo.Code.Once.LinCore.Flat
import qualified MAlonzo.Code.Once.LinCore.FromExpr
import qualified MAlonzo.Code.Once.LinCore.FromIR
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Core.Derived
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Spec.Theory
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Surface.Map
import qualified MAlonzo.Code.Once.Surface.Syntax

-- Once.LinCore.Linear._.Kd
d_Kd_1 a0 = ()
-- Once.LinCore.Linear._.LTy
d_LTy_12 a0 = ()
-- Once.LinCore.Linear._.Arm
d_Arm_50 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.LinCore.Linear._.CP
d_CP_52 a0 a1 a2 a3 a4 a5 a6 = ()
-- Once.LinCore.Linear._.IsPj
d_IsPj_54 a0 a1 a2 a3 a4 = ()
-- Once.LinCore.Linear.Site
d_Site_114 :: MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 -> ()
d_Site_114 = erased
-- Once.LinCore.Linear.sharedIx
d_sharedIx_122 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 -> [Integer]
d_sharedIx_122 ~v0 ~v1 ~v2 v3 v4 v5 = du_sharedIx_122 v3 v4 v5
du_sharedIx_122 ::
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 -> [Integer]
du_sharedIx_122 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'8709'_12
        -> coe
             seq (coe v1)
             (coe
                seq (coe v2) (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v10 v11
                      -> coe
                           MAlonzo.Code.Data.List.Base.du__'43''43'__32
                           (coe
                              MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                              (coe
                                 MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                 (coe MAlonzo.Code.Once.LinCore.FromExpr.du_used'63'_2384 (coe v7))
                                 (coe
                                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                    (coe
                                       MAlonzo.Code.Once.LinCore.FromExpr.du_used'63'_2384
                                       (coe v10))
                                    (coe
                                       MAlonzo.Code.Data.Bool.Base.d_not_22
                                       (coe
                                          MAlonzo.Code.Once.LinCore.FromExpr.du_flat'63'_2260
                                          (coe v5)))))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (0 :: Integer))
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                           (coe
                              MAlonzo.Code.Data.List.Base.du_map_22
                              (coe (\ v12 -> addInt (coe (1 :: Integer)) (coe v12)))
                              (coe du_sharedIx_122 (coe v4) (coe v8) (coe v11)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Linear.capIx
d_capIx_142 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 -> [Integer]
d_capIx_142 ~v0 ~v1 ~v2 v3 v4 = du_capIx_142 v3 v4
du_capIx_142 ::
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 -> [Integer]
du_capIx_142 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Context.C_'8709'_12
        -> coe
             seq (coe v1) (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v6 v7
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe
                       MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                       (coe
                          MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                          (coe MAlonzo.Code.Once.LinCore.FromExpr.du_used'63'_2384 (coe v6))
                          (coe
                             MAlonzo.Code.Data.Bool.Base.d_not_22
                             (coe
                                MAlonzo.Code.Once.LinCore.FromExpr.du_flat'63'_2260 (coe v4))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe (0 :: Integer))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                    (coe
                       MAlonzo.Code.Data.List.Base.du_map_22
                       (coe (\ v8 -> addInt (coe (1 :: Integer)) (coe v8)))
                       (coe du_capIx_142 (coe v3) (coe v7)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Linear.site
d_site_152 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [Integer] -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_site_152 ~v0 v1 v2 = du_site_152 v1 v2
du_site_152 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [Integer] -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_site_152 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Linear.splitSite
d_splitSite_166 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_splitSite_166 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_splitSite_166 v3 v4 v5 v6
du_splitSite_166 ::
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_splitSite_166 v0 v1 v2 v3
  = coe
      du_site_152 (coe v1)
      (coe du_sharedIx_122 (coe v0) (coe v2) (coe v3))
-- Once.LinCore.Linear.isJust
d_isJust_178 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  () -> Maybe AgdaAny -> Bool
d_isJust_178 ~v0 ~v1 v2 = du_isJust_178 v2
du_isJust_178 :: Maybe AgdaAny -> Bool
du_isJust_178 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Linear.isMany
d_isMany_180 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 -> Bool
d_isMany_180 ~v0 v1 = du_isMany_180 v1
du_isMany_180 :: MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 -> Bool
du_isMany_180 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Grade.C_Zero_8
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Grade.C_One_10
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Once.Spec.Grade.C_Many_12
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Linear._.ov
d_ov_198 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Map.T_Map_8 ->
  MAlonzo.Code.Once.Surface.Map.T_Map_8 ->
  MAlonzo.Code.Once.LinCore.FromExpr.T_IsPj_2758 ->
  MAlonzo.Code.Once.LinCore.FromExpr.T_IsPj_2758 -> Bool
d_ov_198 ~v0 ~v1 v2 v3 v4 ~v5 ~v6 v7 v8 = du_ov_198 v2 v3 v4 v7 v8
du_ov_198 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.LinCore.FromExpr.T_IsPj_2758 ->
  MAlonzo.Code.Once.LinCore.FromExpr.T_IsPj_2758 -> Bool
du_ov_198 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.LinCore.FromExpr.C_pj'45'id_2764
        -> case coe v4 of
             MAlonzo.Code.Once.LinCore.FromExpr.C_pj'45'id_2764
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d_not_22
                    (coe MAlonzo.Code.Once.LinCore.FromExpr.du_flat'63'_2260 (coe v0))
             MAlonzo.Code.Once.LinCore.FromExpr.C_pj'45'fst_2770
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d_not_22
                    (coe MAlonzo.Code.Once.LinCore.FromExpr.du_flat'63'_2260 (coe v2))
             MAlonzo.Code.Once.LinCore.FromExpr.C_pj'45'snd_2776
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d_not_22
                    (coe MAlonzo.Code.Once.LinCore.FromExpr.du_flat'63'_2260 (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.FromExpr.C_pj'45'fst_2770
        -> case coe v4 of
             MAlonzo.Code.Once.LinCore.FromExpr.C_pj'45'id_2764
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d_not_22
                    (coe MAlonzo.Code.Once.LinCore.FromExpr.du_flat'63'_2260 (coe v1))
             MAlonzo.Code.Once.LinCore.FromExpr.C_pj'45'fst_2770
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d_not_22
                    (coe MAlonzo.Code.Once.LinCore.FromExpr.du_flat'63'_2260 (coe v1))
             MAlonzo.Code.Once.LinCore.FromExpr.C_pj'45'snd_2776
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.FromExpr.C_pj'45'snd_2776
        -> case coe v4 of
             MAlonzo.Code.Once.LinCore.FromExpr.C_pj'45'id_2764
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d_not_22
                    (coe MAlonzo.Code.Once.LinCore.FromExpr.du_flat'63'_2260 (coe v1))
             MAlonzo.Code.Once.LinCore.FromExpr.C_pj'45'fst_2770
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             MAlonzo.Code.Once.LinCore.FromExpr.C_pj'45'snd_2776
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d_not_22
                    (coe MAlonzo.Code.Once.LinCore.FromExpr.du_flat'63'_2260 (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Linear._.armK
d_armK_234 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Grade.T_ArrowKind_80 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Maybe MAlonzo.Code.Once.LinCore.FromExpr.T_Arm_2842 ->
  (MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
   MAlonzo.Code.Once.Surface.Map.T_Map_8 ->
   MAlonzo.Code.Once.LinCore.FromExpr.T_IsPj_2758 -> Bool) ->
  Bool
d_armK_234 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 ~v7 v8 v9 v10
  = du_armK_234 v5 v6 v8 v9 v10
du_armK_234 ::
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Maybe MAlonzo.Code.Once.LinCore.FromExpr.T_Arm_2842 ->
  (MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
   MAlonzo.Code.Once.Surface.Map.T_Map_8 ->
   MAlonzo.Code.Once.LinCore.FromExpr.T_IsPj_2758 -> Bool) ->
  Bool
du_armK_234 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
        -> case coe v5 of
             MAlonzo.Code.Once.LinCore.FromExpr.C_arm'45'map_2856 v9
               -> case coe v9 of
                    MAlonzo.Code.Once.LinCore.FromExpr.C_pjl_2814 v14
                      -> case coe v2 of
                           MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_276 v20
                             -> coe v4 v1 v20 v14
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.LinCore.FromExpr.C_arm'45'comp_2874 v14
               -> case coe v2 of
                    MAlonzo.Code.Once.Surface.Syntax.C_comp''_306 v17 v18 v20 v23 v24
                      -> case coe v14 of
                           MAlonzo.Code.Once.LinCore.FromExpr.C_pjl_2814 v29
                             -> case coe v24 of
                                  MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_276 v35
                                    -> coe v4 v20 v35 v29
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             v4 v0 (coe MAlonzo.Code.Once.Surface.Map.C_mp'45'id_14)
             (coe MAlonzo.Code.Once.LinCore.FromExpr.C_pj'45'id_2764)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Linear._.cloSite
d_cloSite_268 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Grade.T_Quantity_6 ->
  Bool ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_cloSite_268 ~v0 v1 ~v2 ~v3 v4 v5 ~v6 v7 v8
  = du_cloSite_268 v1 v4 v5 v7 v8
du_cloSite_268 ::
  (MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool) ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  Bool ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_cloSite_268 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8743'__24
         (coe MAlonzo.Code.Data.Bool.Base.d_not_22 (coe v3)) (coe v0 v4))
      (coe
         du_site_152
         (coe
            ("a closure consumes its captures and the program calls closures of its type lent"
             ::
             Data.Text.Text))
         (coe du_capIx_142 (coe v1) (coe v2)))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.LinCore.Linear._.appSite
d_appSite_298 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Maybe MAlonzo.Code.Once.LinCore.FromExpr.T_CP_2708 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_appSite_298 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9 v10 v11
  = du_appSite_298 v4 v5 v6 v7 v9 v10 v11
du_appSite_298 ::
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Maybe MAlonzo.Code.Once.LinCore.FromExpr.T_CP_2708 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_appSite_298 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe
                du_isJust_178
                (coe
                   MAlonzo.Code.Once.LinCore.FromExpr.du_rdw'63'_2380 (coe v3)
                   (coe v5)))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             (coe
                du_splitSite_166 (coe v0)
                (coe ("a case combinator and its argument" :: Data.Text.Text))
                (coe v1)
                (coe
                   MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v2)))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe
                MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                (coe
                   du_isJust_178
                   (coe MAlonzo.Code.Once.LinCore.FromExpr.du_pth'63'_2188 (coe v4)))
                (coe
                   du_isJust_178
                   (coe
                      MAlonzo.Code.Once.LinCore.FromExpr.du_rdx'63'_2422 (coe v0)
                      (coe v3) (coe v1) (coe v2) (coe v5))))
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             (coe
                du_splitSite_166 (coe v0)
                (coe
                   ("the function and the argument of an application"
                    ::
                    Data.Text.Text))
                (coe v1)
                (coe
                   MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Linear._.heldSite
d_heldSite_320 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_heldSite_320 ~v0 v1 v2 v3 = du_heldSite_320 v1 v2 v3
du_heldSite_320 ::
  (MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_heldSite_320 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v0 v2)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Once.LinCore.Linear._.nuSite
d_nuSite_326 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool) ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_nuSite_326 ~v0 ~v1 v2 = du_nuSite_326 v2
du_nuSite_326 ::
  MAlonzo.Code.Once.LinCore.Core.T_LTy_178 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_nuSite_326 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
    coe
      (case coe v0 of
         MAlonzo.Code.Once.LinCore.Core.C_Nu_192 v2
           -> coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe MAlonzo.Code.Once.LinCore.CopyFree.du_coCopies_740 (coe v2))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe
                         ("an unfold whose layer branches: each observation copies its coalgebra"
                          ::
                          Data.Text.Text))
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         _ -> coe v1)
-- Once.LinCore.Linear._.mapSite
d_mapSite_336 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool) ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Map.T_Map_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_mapSite_336 v0 v1 v2 v3 ~v4 v5 = du_mapSite_336 v0 v1 v2 v3 v5
du_mapSite_336 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool) ->
  Integer ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Map.T_Map_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_mapSite_336 v0 v1 v2 v3 v4
  = let v5 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
    coe
      (case coe v4 of
         MAlonzo.Code.Once.Surface.Map.C_mp'45'apply_54
           -> case coe v3 of
                MAlonzo.Code.Once.Spec.Type.C__'42'__22 v9 v10
                  -> case coe v9 of
                       MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v11 v12 v13
                         -> case coe v12 of
                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v14 v15
                                -> case coe v15 of
                                     MAlonzo.Code.Once.Spec.Grade.C_fin_42 v16
                                       -> case coe v16 of
                                            MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                                              -> coe
                                                   du_heldSite_320 (coe v1)
                                                   (coe
                                                      ("an action suspended over a closure, called lent"
                                                       ::
                                                       Data.Text.Text))
                                                   (coe
                                                      MAlonzo.Code.Once.LinCore.FromExpr.d_ty_746
                                                      (coe v0) (coe v2)
                                                      (coe
                                                         MAlonzo.Code.Once.Spec.Core.Derived.du_𝕋_10
                                                         (coe v15) (coe v13)))
                                            _ -> coe v5
                                     MAlonzo.Code.Once.Spec.Grade.C_eff_44
                                       -> coe
                                            du_heldSite_320 (coe v1)
                                            (coe
                                               ("an action suspended over a closure, called lent"
                                                ::
                                                Data.Text.Text))
                                            (coe
                                               MAlonzo.Code.Once.LinCore.FromExpr.d_ty_746 (coe v0)
                                               (coe v2)
                                               (coe
                                                  MAlonzo.Code.Once.Spec.Core.Derived.du_𝕋_10
                                                  (coe v15) (coe v13)))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v5
                _ -> coe v5
         MAlonzo.Code.Once.Surface.Map.C_mp'45'Out_68 v6 v9
           -> case coe v3 of
                MAlonzo.Code.Once.Spec.Type.C_ν_30 v10 v11
                  -> case coe v11 of
                       MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38
                         -> coe
                              du_heldSite_320 (coe v1)
                              (coe
                                 ("an unfolding suspended over its stream, called lent"
                                  ::
                                  Data.Text.Text))
                              (coe
                                 MAlonzo.Code.Once.LinCore.FromExpr.d_ty_746 (coe v0) (coe v2)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Core.Derived.du_𝕋_10
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_fin_42 (coe v11))
                                    (coe
                                       MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v10)
                                       (coe v3))))
                       _ -> coe v5
                _ -> coe v5
         _ -> coe v5)
-- Once.LinCore.Linear._.sitesFn
d_sitesFn_358 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  Maybe MAlonzo.Code.Once.LinCore.FromExpr.T_CP_2708 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_sitesFn_358 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v9 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
        -> coe
             seq (coe v10)
             (case coe v6 of
                MAlonzo.Code.Once.Spec.Type.C__'43'__24 v11 v12
                  -> case coe v8 of
                       MAlonzo.Code.Once.Surface.Syntax.C_copair''_324 v15 v16 v21 v22
                         -> coe
                              MAlonzo.Code.Data.List.Base.du__'43''43'__32
                              (coe
                                 d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v15)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v11)
                                    (coe
                                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                       (coe
                                          MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                          (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                                    (coe v7))
                                 (coe v21))
                              (coe
                                 d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v16)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v12)
                                    (coe
                                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                       (coe
                                          MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                          (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                                    (coe v7))
                                 (coe v22))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe
                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v6)
                (coe
                   MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                   (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                   (coe
                      MAlonzo.Code.Once.Spec.Grade.C_fin_42
                      (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                (coe v7))
             (coe v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Linear._.sites
d_sites_370 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_sites_370 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_20 v10
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Surface.Syntax.C_lam_38 v11 v17
        -> case coe v6 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v18 v19 v20
               -> case coe v11 of
                    MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                      -> coe
                           MAlonzo.Code.Data.List.Base.du__'43''43'__32
                           (coe
                              d_sites_370 (coe v0) (coe v1) (coe v2)
                              (coe addInt (coe (1 :: Integer)) (coe v3))
                              (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v4 v18)
                              (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v11 v5) (coe v20)
                              (coe v17))
                           (coe
                              du_cloSite_268 (coe v1) (coe v4) (coe v5)
                              (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                              (coe
                                 MAlonzo.Code.Once.LinCore.FromExpr.d_ty_746 (coe v0) (coe v2)
                                 (coe v6)))
                    MAlonzo.Code.Once.Spec.Grade.C_One_10
                      -> coe
                           MAlonzo.Code.Data.List.Base.du__'43''43'__32
                           (coe
                              d_sites_370 (coe v0) (coe v1) (coe v2)
                              (coe addInt (coe (1 :: Integer)) (coe v3))
                              (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v4 v18)
                              (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v11 v5) (coe v20)
                              (coe v17))
                           (coe
                              du_cloSite_268 (coe v1) (coe v4) (coe v5)
                              (coe
                                 du_isJust_178
                                 (coe
                                    MAlonzo.Code.Once.LinCore.FromExpr.du_rdl'63'_2464 (coe v4)
                                    (coe v5) (coe v20) (coe v17)))
                              (coe
                                 MAlonzo.Code.Once.LinCore.FromExpr.d_ty_746 (coe v0) (coe v2)
                                 (coe v6)))
                    MAlonzo.Code.Once.Spec.Grade.C_Many_12
                      -> coe
                           MAlonzo.Code.Data.List.Base.du__'43''43'__32
                           (coe
                              d_sites_370 (coe v0) (coe v1) (coe v2)
                              (coe addInt (coe (1 :: Integer)) (coe v3))
                              (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v4 v18)
                              (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v11 v5) (coe v20)
                              (coe v17))
                           (coe
                              du_cloSite_268 (coe v1) (coe v4) (coe v5)
                              (coe
                                 du_isJust_178
                                 (coe
                                    MAlonzo.Code.Once.LinCore.FromExpr.du_rdl'63'_2464 (coe v4)
                                    (coe v5) (coe v20) (coe v17)))
                              (coe
                                 MAlonzo.Code.Once.LinCore.FromExpr.d_ty_746 (coe v0) (coe v2)
                                 (coe v6)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_54 v10 v11 v12 v14 v15 v16
        -> case coe v14 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe
                    d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v10)
                    (coe
                       MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v12)
                       (coe
                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v14)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_fin_42
                             (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                       (coe v6))
                    (coe v15)
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe
                       d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v10)
                       (coe
                          MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v12)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v14)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                          (coe v6))
                       (coe v15))
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v11)
                          (coe v12) (coe v16))
                       (coe
                          du_splitSite_166 (coe v4)
                          (coe
                             ("the function and the argument of an application"
                              ::
                              Data.Text.Text))
                          (coe v10)
                          (coe
                             MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v14)
                             (coe v11))))
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe
                       d_sitesFn_358 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                       (coe v10) (coe v12) (coe v6) (coe v15)
                       (coe
                          MAlonzo.Code.Once.LinCore.FromExpr.du_cp'63'_2746 (coe v0) (coe v2)
                          (coe v3) (coe v4)
                          (coe
                             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v12)
                             (coe
                                MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v14)
                                (coe
                                   MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                   (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                             (coe v6))
                          (coe v15)))
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v11)
                          (coe v12) (coe v16))
                       (coe
                          du_appSite_298 (coe v4) (coe v10) (coe v11) (coe v12) (coe v15)
                          (coe v16)
                          (coe
                             MAlonzo.Code.Once.LinCore.FromExpr.du_cp'63'_2746 (coe v0) (coe v2)
                             (coe v3) (coe v4)
                             (coe
                                MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v12)
                                (coe
                                   MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v14)
                                   (coe
                                      MAlonzo.Code.Once.Spec.Grade.C_fin_42
                                      (coe MAlonzo.Code.Once.Spec.Grade.C_pure'7584'_36)))
                                (coe v6))
                             (coe v15))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_74 v10 v11 v12 v14 v16 v17 v18
        -> case coe v6 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v19 v20 v21
               -> case coe v20 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v22 v23
                      -> case coe v14 of
                           MAlonzo.Code.Once.Spec.Grade.C_Zero_8
                             -> coe
                                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                  (coe
                                     d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                     (coe v10)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v12)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v14)
                                           (coe v23))
                                        (coe v21))
                                     (coe v17))
                                  (coe
                                     du_cloSite_268 (coe v1) (coe v4) (coe v10)
                                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                     (coe
                                        MAlonzo.Code.Once.LinCore.Core.C_Fn_190
                                        (coe MAlonzo.Code.Once.LinCore.Core.C_many_154)
                                        (coe
                                           MAlonzo.Code.Once.LinCore.FromIR.du_grade_952 (coe v23))
                                        (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                                        (coe
                                           MAlonzo.Code.Once.LinCore.FromExpr.d_ty_746 (coe v0)
                                           (coe v2) (coe v21))))
                           MAlonzo.Code.Once.Spec.Grade.C_One_10
                             -> coe
                                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                  (coe
                                     d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                     (coe v10)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v12)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v14)
                                           (coe v23))
                                        (coe v21))
                                     (coe v17))
                                  (coe
                                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                     (coe
                                        d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                        (coe v11) (coe v12) (coe v18))
                                     (coe
                                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                        (coe
                                           du_splitSite_166 (coe v4)
                                           (coe
                                              ("the function and the argument of a suspended application"
                                               ::
                                               Data.Text.Text))
                                           (coe v10)
                                           (coe
                                              MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                              (coe v14) (coe v11)))
                                        (coe
                                           du_cloSite_268 (coe v1) (coe v4)
                                           (coe
                                              MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                              (coe v10)
                                              (coe
                                                 MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                 (coe v14) (coe v11)))
                                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                           (coe
                                              MAlonzo.Code.Once.LinCore.Core.C_Fn_190
                                              (coe MAlonzo.Code.Once.LinCore.Core.C_many_154)
                                              (coe
                                                 MAlonzo.Code.Once.LinCore.FromIR.du_grade_952
                                                 (coe v23))
                                              (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                                              (coe
                                                 MAlonzo.Code.Once.LinCore.FromExpr.d_ty_746
                                                 (coe v0) (coe v2) (coe v21))))))
                           MAlonzo.Code.Once.Spec.Grade.C_Many_12
                             -> coe
                                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                  (coe
                                     d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                     (coe v10)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v12)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 (coe v14)
                                           (coe v23))
                                        (coe v21))
                                     (coe v17))
                                  (coe
                                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                     (coe
                                        d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                        (coe v11) (coe v12) (coe v18))
                                     (coe
                                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                        (coe
                                           du_splitSite_166 (coe v4)
                                           (coe
                                              ("the function and the argument of a suspended application"
                                               ::
                                               Data.Text.Text))
                                           (coe v10)
                                           (coe
                                              MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                              (coe v14) (coe v11)))
                                        (coe
                                           du_cloSite_268 (coe v1) (coe v4)
                                           (coe
                                              MAlonzo.Code.Once.Spec.Context.du__'43''7512'__60
                                              (coe v10)
                                              (coe
                                                 MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                                 (coe v14) (coe v11)))
                                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                           (coe
                                              MAlonzo.Code.Once.LinCore.Core.C_Fn_190
                                              (coe MAlonzo.Code.Once.LinCore.Core.C_many_154)
                                              (coe
                                                 MAlonzo.Code.Once.LinCore.FromIR.du_grade_952
                                                 (coe v23))
                                              (coe MAlonzo.Code.Once.LinCore.Core.C_One_180)
                                              (coe
                                                 MAlonzo.Code.Once.LinCore.FromExpr.d_ty_746
                                                 (coe v0) (coe v2) (coe v21))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_88 v10 v11 v14 v15
        -> case coe v6 of
             MAlonzo.Code.Once.Spec.Type.C__'42'__22 v16 v17
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe
                       d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v10)
                       (coe v16) (coe v14))
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v11)
                          (coe v17) (coe v15))
                       (coe
                          MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                          (coe
                             du_isJust_178
                             (coe
                                MAlonzo.Code.Once.LinCore.FromExpr.du_rdw'63'_2380 (coe v16)
                                (coe v14)))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                          (coe
                             du_splitSite_166 (coe v4)
                             (coe ("the two components of a pair" :: Data.Text.Text)) (coe v10)
                             (coe v11))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_100 v12 v13
        -> coe
             d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v6) (coe v12))
             (coe v13)
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_112 v11 v13
        -> coe
             d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v11) (coe v6))
             (coe v13)
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_124 v13
        -> case coe v6 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v14 v15
               -> coe
                    d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                    (coe v14) (coe v13)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_136 v13
        -> case coe v6 of
             MAlonzo.Code.Once.Spec.Type.C__'43'__24 v14 v15
               -> coe
                    d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
                    (coe v15) (coe v13)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_158 v10 v11 v12 v13 v14 v15 v16 v18 v19 v20
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe
                d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v10)
                (coe MAlonzo.Code.Once.Spec.Type.C__'43'__24 (coe v15) (coe v16))
                (coe v18))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   d_sites_370 (coe v0) (coe v1) (coe v2)
                   (coe addInt (coe (1 :: Integer)) (coe v3))
                   (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v4 v15)
                   (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v13 v11) (coe v6)
                   (coe v19))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe
                      d_sites_370 (coe v0) (coe v1) (coe v2)
                      (coe addInt (coe (1 :: Integer)) (coe v3))
                      (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v4 v16)
                      (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v14 v12) (coe v6)
                      (coe v20))
                   (coe
                      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                      (coe
                         du_isJust_178
                         (coe
                            MAlonzo.Code.Once.LinCore.FromExpr.du_rdw'63'_2380
                            (coe MAlonzo.Code.Once.Spec.Type.C__'43'__24 (coe v15) (coe v16))
                            (coe v18)))
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                      (coe
                         du_splitSite_166 (coe v4)
                         (coe ("a case's scrutinee and its arms" :: Data.Text.Text))
                         (coe v10)
                         (coe
                            MAlonzo.Code.Once.Context.du__'8852''7512'__22 (coe v11)
                            (coe v12))))))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_164
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_174 v12
        -> coe
             d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe MAlonzo.Code.Once.Spec.Type.C_Void_20) (coe v12)
      MAlonzo.Code.Once.Surface.Syntax.C_let''_190 v10 v11 v12 v13 v15 v16
        -> case coe v12 of
             MAlonzo.Code.Once.Spec.Grade.C_Zero_8
               -> coe
                    d_sites_370 (coe v0) (coe v1) (coe v2)
                    (coe addInt (coe (1 :: Integer)) (coe v3))
                    (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v4 v13)
                    (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v12 v11) (coe v6)
                    (coe v16)
             MAlonzo.Code.Once.Spec.Grade.C_One_10
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe
                       d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v10)
                       (coe v13) (coe v15))
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          d_sites_370 (coe v0) (coe v1) (coe v2)
                          (coe addInt (coe (1 :: Integer)) (coe v3))
                          (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v4 v13)
                          (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v12 v11) (coe v6)
                          (coe v16))
                       (coe
                          du_splitSite_166 (coe v4)
                          (coe ("a let's body and its binding" :: Data.Text.Text)) (coe v11)
                          (coe
                             MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v12)
                             (coe v10))))
             MAlonzo.Code.Once.Spec.Grade.C_Many_12
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe
                       d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v10)
                       (coe v13) (coe v15))
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe
                          d_sites_370 (coe v0) (coe v1) (coe v2)
                          (coe addInt (coe (1 :: Integer)) (coe v3))
                          (coe MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v4 v13)
                          (coe MAlonzo.Code.Once.Spec.Context.C__'8759'__40 v12 v11) (coe v6)
                          (coe v16))
                       (coe
                          du_splitSite_166 (coe v4)
                          (coe ("a let's body and its binding" :: Data.Text.Text)) (coe v11)
                          (coe
                             MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72 (coe v12)
                             (coe v10))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_int_196 v10
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Surface.Syntax.C_float_204 v10
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Surface.Syntax.C_num_218 v11 v12 v13 v14 v15 v16
        -> coe
             d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe
                MAlonzo.Code.Once.Spec.Theory.du_symDom_86 (coe v11) (coe v13))
             (coe v16)
      MAlonzo.Code.Once.Surface.Syntax.C_coerce_230 v11 v13 v14
        -> coe
             d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
             (coe v11) (coe v14)
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_238 v10 v11 v12
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Surface.Syntax.C_closure_246 v11
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Surface.Syntax.C_poly_256 v10
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Once.Surface.Syntax.C_closed_264 v11
        -> coe
             d_sites_370 (coe v0) (coe v1) (coe v2) (coe (0 :: Integer))
             (coe MAlonzo.Code.Once.Spec.Context.C_'8709'_12)
             (coe MAlonzo.Code.Once.Spec.Context.C_'91''93'_36) (coe v6)
             (coe v11)
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_276 v13
        -> case coe v6 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v14 v15 v16
               -> coe
                    du_mapSite_336 (coe v0) (coe v1) (coe v2) (coe v14) (coe v13)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_288 v10 v11 v13 v14
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe
                d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v10)
                (coe v11) (coe v14))
             (coe du_mapSite_336 (coe v0) (coe v1) (coe v2) (coe v11) (coe v13))
      MAlonzo.Code.Once.Surface.Syntax.C_comp''_306 v10 v11 v13 v16 v17
        -> case coe v6 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v18 v19 v20
               -> case coe v19 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v21 v22
                      -> coe
                           MAlonzo.Code.Data.List.Base.du__'43''43'__32
                           (coe
                              d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v10)
                              (coe
                                 MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v13)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v22))
                                 (coe v20))
                              (coe v16))
                           (coe
                              MAlonzo.Code.Data.List.Base.du__'43''43'__32
                              (coe
                                 d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v11)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v18)
                                    (coe
                                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v22))
                                    (coe v13))
                                 (coe v17))
                              (coe
                                 du_splitSite_166 (coe v4)
                                 (coe ("the two closures of a composition" :: Data.Text.Text))
                                 (coe v10)
                                 (coe
                                    MAlonzo.Code.Once.Spec.Context.du__'42''7512'__72
                                    (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v11))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_copair''_324 v10 v11 v16 v17
        -> case coe v6 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v18 v19 v20
               -> case coe v18 of
                    MAlonzo.Code.Once.Spec.Type.C__'43'__24 v21 v22
                      -> case coe v19 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v23 v24
                             -> coe
                                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                  (coe
                                     d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                     (coe v10)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v21)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v24))
                                        (coe v20))
                                     (coe v16))
                                  (coe
                                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                     (coe
                                        d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                        (coe v11)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                           (coe v22)
                                           (coe
                                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                              (coe v24))
                                           (coe v20))
                                        (coe v17))
                                     (coe
                                        du_splitSite_166 (coe v4)
                                        (coe
                                           ("the two arms of a case combinator" :: Data.Text.Text))
                                        (coe v10) (coe v11)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fork''_342 v10 v11 v16 v17
        -> case coe v6 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v18 v19 v20
               -> case coe v19 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v21 v22
                      -> case coe v20 of
                           MAlonzo.Code.Once.Spec.Type.C__'42'__22 v23 v24
                             -> coe
                                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                  (coe
                                     d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                     (coe v10)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v18)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v22))
                                        (coe v23))
                                     (coe v16))
                                  (coe
                                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                     (coe
                                        d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                        (coe v11)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                           (coe v18)
                                           (coe
                                              MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                              (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                              (coe v22))
                                           (coe v24))
                                        (coe v17))
                                     (coe
                                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                        (coe
                                           du_splitSite_166 (coe v4)
                                           (coe ("the two arms of a fork" :: Data.Text.Text))
                                           (coe v10) (coe v11))
                                        (coe
                                           MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                           (coe
                                              du_armK_234 (coe v18) (coe v23) (coe v16)
                                              (coe
                                                 MAlonzo.Code.Once.LinCore.FromExpr.du_arm'63'_2888
                                                 (coe
                                                    MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                    (coe v18)
                                                    (coe
                                                       MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                       (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                       (coe v22))
                                                    (coe v23))
                                                 (coe v16))
                                              (coe
                                                 (\ v25 v26 v27 ->
                                                    coe
                                                      du_armK_234 (coe v18) (coe v24) (coe v17)
                                                      (coe
                                                         MAlonzo.Code.Once.LinCore.FromExpr.du_arm'63'_2888
                                                         (coe
                                                            MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                            (coe v18)
                                                            (coe
                                                               MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                               (coe
                                                                  MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                               (coe v22))
                                                            (coe v24))
                                                         (coe v17))
                                                      (coe
                                                         (\ v28 v29 ->
                                                            coe
                                                              du_ov_198 (coe v18) (coe v25)
                                                              (coe v28) (coe v27))))))
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe
                                                    ("a fork's two arms take overlapping parts of its argument"
                                                     ::
                                                     Data.Text.Text))
                                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_curry''_360 v16
        -> case coe v6 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v17 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v20 v21
                      -> case coe v19 of
                           MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v22 v23 v24
                             -> case coe v23 of
                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v25 v26
                                    -> coe
                                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                         (coe
                                            d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                            (coe v5)
                                            (coe
                                               MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                               (coe
                                                  MAlonzo.Code.Once.Spec.Type.C__'42'__22 (coe v17)
                                                  (coe v22))
                                               (coe
                                                  MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                  (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                  (coe v26))
                                               (coe v24))
                                            (coe v16))
                                         (coe
                                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                            (coe
                                               du_heldSite_320 (coe v1)
                                               (coe
                                                  ("a curried closure over its function, called lent"
                                                   ::
                                                   Data.Text.Text))
                                               (coe
                                                  MAlonzo.Code.Once.LinCore.FromExpr.d_ty_746
                                                  (coe v0) (coe v2)
                                                  (coe
                                                     MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                     (coe v17)
                                                     (coe
                                                        MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                        (coe v21))
                                                     (coe
                                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                        (coe v22)
                                                        (coe
                                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                           (coe
                                                              MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                           (coe v26))
                                                        (coe v24)))))
                                            (coe
                                               du_heldSite_320 (coe v1)
                                               (coe
                                                  ("a curried closure over its function and first argument, called lent"
                                                   ::
                                                   Data.Text.Text))
                                               (coe
                                                  MAlonzo.Code.Once.LinCore.FromExpr.d_ty_746
                                                  (coe v0) (coe v2)
                                                  (coe
                                                     MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                                     (coe v22)
                                                     (coe
                                                        MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                        (coe v26))
                                                     (coe v24)))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_cata_376 v10 v12 v15 v16
        -> case coe v6 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v17 v18 v19
               -> case coe v17 of
                    MAlonzo.Code.Once.Spec.Type.C_μ_28 v20
                      -> case coe v18 of
                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v21 v22
                             -> coe
                                  d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v10)
                                  (coe
                                     MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50 (coe v20)
                                        (coe v19))
                                     (coe
                                        MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                        (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12) (coe v22))
                                     (coe v19))
                                  (coe v16)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_ana_394 v10 v12 v16 v17
        -> case coe v6 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v18 v19 v20
               -> case coe v19 of
                    MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90 v21 v22
                      -> case coe v20 of
                           MAlonzo.Code.Once.Spec.Type.C_ν_30 v23 v24
                             -> coe
                                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                  (coe
                                     d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                                     (coe v10)
                                     (coe
                                        MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v18)
                                        (coe
                                           MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_fin_42 (coe v24)))
                                        (coe
                                           MAlonzo.Code.Once.Spec.Type.du_'10214'_'10215'F_50
                                           (coe v23) (coe v18)))
                                     (coe v17))
                                  (coe
                                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                     (coe
                                        du_heldSite_320 (coe v1)
                                        (coe
                                           ("an unfold over its coalgebra, called lent"
                                            ::
                                            Data.Text.Text))
                                        (coe
                                           MAlonzo.Code.Once.LinCore.FromExpr.d_ty_746 (coe v0)
                                           (coe v2)
                                           (coe
                                              MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26
                                              (coe v18)
                                              (coe
                                                 MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                                                 (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                                                 (coe v22))
                                              (coe v20))))
                                     (coe
                                        du_nuSite_326
                                        (coe
                                           MAlonzo.Code.Once.LinCore.FromExpr.d_ty_746 (coe v0)
                                           (coe v2) (coe v20))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_loop_406 v10 v13
        -> case coe v6 of
             MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 v14 v15 v16
               -> coe
                    d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v10)
                    (coe
                       MAlonzo.Code.Once.Spec.Type.C__'8658''91'_'93'__26 (coe v14)
                       (coe
                          MAlonzo.Code.Once.Spec.Grade.C_mk'45'kind_90
                          (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)
                          (coe
                             MAlonzo.Code.Once.Spec.Grade.C_fin_42
                             (coe MAlonzo.Code.Once.Spec.Grade.C_act'7584'_38)))
                       (coe MAlonzo.Code.Once.Spec.Type.C__'43'__24 (coe v16) (coe v14)))
                    (coe v13)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Linear._.linear?
d_linear'63'_644 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 -> Bool
d_linear'63'_644 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      du_nullL_652
      (coe
         d_sites_370 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
         (coe v6) (coe v7))
-- Once.LinCore.Linear._._.nullL
d_nullL_652 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Core.T_LTy_178 -> Bool) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  MAlonzo.Code.Once.Spec.Context.T_Usage_34 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_10 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> Bool
d_nullL_652 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_nullL_652 v8
du_nullL_652 :: [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> Bool
du_nullL_652 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v1 v2 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
