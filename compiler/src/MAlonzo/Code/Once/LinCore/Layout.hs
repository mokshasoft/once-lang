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

module MAlonzo.Code.Once.LinCore.Layout where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.LinCore.Code
import qualified MAlonzo.Code.Once.LinCore.Core
import qualified MAlonzo.Code.Once.LinCore.Flat
import qualified MAlonzo.Code.Once.LinCore.Image
import qualified MAlonzo.Code.Once.Spec.Numerics

-- Once.LinCore.Layout._.LTy
d_LTy_74 a0 a1 = ()
-- Once.LinCore.Layout._.Sh
d_Sh_746 a0 a1 = ()
-- Once.LinCore.Layout._.Sh.env
d_env_752 ::
  MAlonzo.Code.Once.LinCore.Code.T_Sh_882 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_174]
d_env_752 v0
  = coe MAlonzo.Code.Once.LinCore.Code.d_env_888 (coe v0)
-- Once.LinCore.Layout._.Sh.ops
d_ops_754 ::
  MAlonzo.Code.Once.LinCore.Code.T_Sh_882 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_174]
d_ops_754 v0
  = coe MAlonzo.Code.Once.LinCore.Code.d_ops_890 (coe v0)
-- Once.LinCore.Layout._.Codeᴵ
d_Code'7477'_768 a0 a1 a2 a3 = ()
-- Once.LinCore.Layout._.Insᴵ
d_Ins'7477'_770 a0 a1 a2 a3 = ()
-- Once.LinCore.Layout.wsz
d_wsz_1016 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Core.T_LTy_174 -> Integer
d_wsz_1016 ~v0 ~v1 v2 = du_wsz_1016 v2
du_wsz_1016 :: MAlonzo.Code.Once.LinCore.Core.T_LTy_174 -> Integer
du_wsz_1016 v0
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Core.C_One_176 -> coe (0 :: Integer)
      MAlonzo.Code.Once.LinCore.Core.C_Zero_178 -> coe (0 :: Integer)
      MAlonzo.Code.Once.LinCore.Core.C__'8855't__180 v1 v2
        -> coe addInt (coe du_wsz_1016 (coe v1)) (coe du_wsz_1016 (coe v2))
      MAlonzo.Code.Once.LinCore.Core.C__'8853't__182 v1 v2
        -> coe
             addInt (coe (1 :: Integer))
             (coe
                MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                (coe du_wsz_1016 (coe v1)) (coe du_wsz_1016 (coe v2)))
      MAlonzo.Code.Once.LinCore.Core.C_Ct_184 v1 v2
        -> coe du_wsz_1016 (coe v2)
      MAlonzo.Code.Once.LinCore.Core.C_Fn_186 v1 v2 v3 v4
        -> coe (1 :: Integer)
      MAlonzo.Code.Once.LinCore.Core.C_Nu_188 v1 -> coe (1 :: Integer)
      MAlonzo.Code.Once.LinCore.Core.C_μt_190 v1 -> coe (1 :: Integer)
      MAlonzo.Code.Once.LinCore.Core.C_Bt_192 v1 -> coe (1 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Layout.ws
d_ws_1044 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_174] -> Integer
d_ws_1044 ~v0 ~v1 v2 = du_ws_1044 v2
du_ws_1044 :: [MAlonzo.Code.Once.LinCore.Core.T_LTy_174] -> Integer
du_ws_1044 v0
  = case coe v0 of
      [] -> coe (0 :: Integer)
      (:) v1 v2
        -> coe addInt (coe du_ws_1044 (coe v2)) (coe du_wsz_1016 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Layout.envW
d_envW_1050 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_882 -> Integer
d_envW_1050 ~v0 ~v1 v2 = du_envW_1050 v2
du_envW_1050 :: MAlonzo.Code.Once.LinCore.Code.T_Sh_882 -> Integer
du_envW_1050 v0
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Code.C__'8739'__892 v1 v2
        -> coe du_ws_1044 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Layout.opW
d_opW_1056 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_882 -> Integer
d_opW_1056 ~v0 ~v1 v2 = du_opW_1056 v2
du_opW_1056 :: MAlonzo.Code.Once.LinCore.Code.T_Sh_882 -> Integer
du_opW_1056 v0
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Code.C__'8739'__892 v1 v2
        -> coe du_ws_1044 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Layout._⊔²_
d__'8852''178'__1062 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'8852''178'__1062 ~v0 ~v1 v2 v3 = du__'8852''178'__1062 v2 v3
du__'8852''178'__1062 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du__'8852''178'__1062 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v2) (coe v4))
                    (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Layout.at
d_at_1072 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_882 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_at_1072 ~v0 ~v1 v2 = du_at_1072 v2
du_at_1072 ::
  MAlonzo.Code.Once.LinCore.Code.T_Sh_882 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_at_1072 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_envW_1050 (coe v0)) (coe du_opW_1056 (coe v0))
-- Once.LinCore.Layout.peakI
d_peakI_1080 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_882 ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_882 ->
  MAlonzo.Code.Once.LinCore.Image.T_Ins'7477'_1122 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_peakI_1080 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
              (coe (0 :: Integer)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Once.LinCore.Image.C_swap_1152
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Code.C__'8739'__892 v10 v11
                  -> case coe v11 of
                       (:) v12 v13
                         -> case coe v13 of
                              (:) v14 v15
                                -> case coe v3 of
                                     MAlonzo.Code.Once.LinCore.Code.C__'8739'__892 v16 v17
                                       -> case coe v17 of
                                            (:) v18 v19
                                              -> case coe v19 of
                                                   (:) v20 v21
                                                     -> coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe (0 :: Integer))
                                                          (coe
                                                             addInt (coe du_ws_1044 (coe v11))
                                                             (coe du_wsz_1016 (coe v12)))
                                                   _ -> coe v5
                                            _ -> coe v5
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> coe v5
                       _ -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.LinCore.Image.C_prim_1172 v6 v7 v12
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Code.C__'8739'__892 v13 v14
                  -> case coe v14 of
                       (:) v15 v16
                         -> case coe v3 of
                              MAlonzo.Code.Once.LinCore.Code.C__'8739'__892 v17 v18
                                -> case coe v18 of
                                     (:) v19 v20
                                       -> case coe v12 of
                                            MAlonzo.Code.Once.LinCore.Core.C_lswap_856
                                              -> case coe v15 of
                                                   MAlonzo.Code.Once.LinCore.Core.C__'8855't__180 v24 v25
                                                     -> case coe v19 of
                                                          MAlonzo.Code.Once.LinCore.Core.C__'8855't__180 v26 v27
                                                            -> coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe (0 :: Integer))
                                                                 (coe
                                                                    addInt
                                                                    (coe du_ws_1044 (coe v14))
                                                                    (coe du_wsz_1016 (coe v24)))
                                                          _ -> coe v5
                                                   _ -> coe v5
                                            _ -> coe v5
                                     _ -> coe v5
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.LinCore.Image.C_loop_1464 v11
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Code.C__'8739'__892 v12 v13
                  -> case coe v12 of
                       (:) v14 v15
                         -> case coe v13 of
                              (:) v16 v17
                                -> case coe v3 of
                                     MAlonzo.Code.Once.LinCore.Code.C__'8739'__892 v18 v19
                                       -> case coe v18 of
                                            (:) v20 v21
                                              -> case coe v19 of
                                                   (:) v22 v23
                                                     -> coe
                                                          du_peakC_1086 (coe v0) (coe v1) (coe v2)
                                                          (coe v11)
                                                   _ -> coe v5
                                            _ -> coe v5
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> coe v5
                       _ -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v5)
-- Once.LinCore.Layout.peakC
d_peakC_1086 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_882 ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_882 ->
  MAlonzo.Code.Once.LinCore.Image.T_Code'7477'_1120 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_peakC_1086 v0 v1 v2 ~v3 v4 = du_peakC_1086 v0 v1 v2 v4
du_peakC_1086 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_882 ->
  MAlonzo.Code.Once.LinCore.Image.T_Code'7477'_1120 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_peakC_1086 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.LinCore.Image.C_end_1474
        -> coe du_at_1072 (coe v2)
      MAlonzo.Code.Once.LinCore.Image.C__'10814'__1482 v5 v7 v8
        -> coe
             du__'8852''178'__1062 (coe du_at_1072 (coe v2))
             (coe
                du__'8852''178'__1062
                (coe d_peakI_1080 (coe v0) (coe v1) (coe v2) (coe v5) (coe v7))
                (coe du_peakC_1086 (coe v0) (coe v1) (coe v5) (coe v8)))
      MAlonzo.Code.Once.LinCore.Image.C_case_1494 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.LinCore.Code.C__'8739'__892 v11 v12
               -> case coe v12 of
                    (:) v13 v14
                      -> case coe v13 of
                           MAlonzo.Code.Once.LinCore.Core.C__'8853't__182 v15 v16
                             -> coe
                                  du__'8852''178'__1062 (coe du_at_1072 (coe v2))
                                  (coe
                                     du__'8852''178'__1062
                                     (coe
                                        du_peakC_1086 (coe v0) (coe v1)
                                        (coe
                                           MAlonzo.Code.Once.LinCore.Code.C__'8739'__892 (coe v11)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v15)
                                              (coe v14)))
                                        (coe v9))
                                     (coe
                                        du_peakC_1086 (coe v0) (coe v1)
                                        (coe
                                           MAlonzo.Code.Once.LinCore.Code.C__'8739'__892 (coe v11)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v16)
                                              (coe v14)))
                                        (coe v10)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Image.C_ecase_1506 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.LinCore.Code.C__'8739'__892 v11 v12
               -> case coe v11 of
                    (:) v13 v14
                      -> case coe v13 of
                           MAlonzo.Code.Once.LinCore.Core.C__'8853't__182 v15 v16
                             -> coe
                                  du__'8852''178'__1062 (coe du_at_1072 (coe v2))
                                  (coe
                                     du__'8852''178'__1062
                                     (coe
                                        du_peakC_1086 (coe v0) (coe v1)
                                        (coe
                                           MAlonzo.Code.Once.LinCore.Code.C__'8739'__892
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v15)
                                              (coe v11))
                                           (coe v12))
                                        (coe v9))
                                     (coe
                                        du_peakC_1086 (coe v0) (coe v1)
                                        (coe
                                           MAlonzo.Code.Once.LinCore.Code.C__'8739'__892
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v16)
                                              (coe v11))
                                           (coe v12))
                                        (coe v10)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Image.C_halted_1512
        -> coe du_at_1072 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Layout.Frame
d_Frame_1126 a0 a1 = ()
data T_Frame_1126 = C_frame_1136 Integer Integer
-- Once.LinCore.Layout.Frame.EP
d_EP_1132 :: T_Frame_1126 -> Integer
d_EP_1132 v0
  = case coe v0 of
      C_frame_1136 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Layout.Frame.OP
d_OP_1134 :: T_Frame_1126 -> Integer
d_OP_1134 v0
  = case coe v0 of
      C_frame_1136 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Layout.budget
d_budget_1138 :: T_Frame_1126 -> Integer
d_budget_1138 v0
  = coe addInt (coe d_OP_1134 (coe v0)) (coe d_EP_1132 (coe v0))
-- Once.LinCore.Layout.frameOf
d_frameOf_1146 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_882 ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_882 ->
  MAlonzo.Code.Once.LinCore.Image.T_Code'7477'_1120 -> T_Frame_1126
d_frameOf_1146 v0 v1 v2 ~v3 v4 = du_frameOf_1146 v0 v1 v2 v4
du_frameOf_1146 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_882 ->
  MAlonzo.Code.Once.LinCore.Image.T_Code'7477'_1120 -> T_Frame_1126
du_frameOf_1146 v0 v1 v2 v3
  = coe
      C_frame_1136
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe du_peakC_1086 (coe v0) (coe v1) (coe v2) (coe v3)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe du_peakC_1086 (coe v0) (coe v1) (coe v2) (coe v3)))
-- Once.LinCore.Layout.envAt
d_envAt_1150 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_174] -> Integer
d_envAt_1150 ~v0 ~v1 v2 = du_envAt_1150 v2
du_envAt_1150 ::
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_174] -> Integer
du_envAt_1150 v0 = coe du_ws_1044 (coe v0)
-- Once.LinCore.Layout.opAt
d_opAt_1154 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  T_Frame_1126 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_174] -> Integer
d_opAt_1154 ~v0 ~v1 v2 v3 = du_opAt_1154 v2 v3
du_opAt_1154 ::
  T_Frame_1126 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_174] -> Integer
du_opAt_1154 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
      (addInt (coe d_OP_1134 (coe v0)) (coe d_EP_1132 (coe v0)))
      (coe du_ws_1044 (coe v1))
