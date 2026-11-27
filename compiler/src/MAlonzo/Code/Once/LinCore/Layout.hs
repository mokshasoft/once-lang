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
import qualified MAlonzo.Code.Once.LinCore.Values
import qualified MAlonzo.Code.Once.Spec.Numerics

-- Once.LinCore.Layout._.LTy
d_LTy_74 a0 a1 = ()
-- Once.LinCore.Layout._.Sh
d_Sh_700 a0 a1 = ()
-- Once.LinCore.Layout._.Sh.env
d_env_706 ::
  MAlonzo.Code.Once.LinCore.Code.T_Sh_850 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178]
d_env_706 v0
  = coe MAlonzo.Code.Once.LinCore.Code.d_env_856 (coe v0)
-- Once.LinCore.Layout._.Sh.ops
d_ops_708 ::
  MAlonzo.Code.Once.LinCore.Code.T_Sh_850 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178]
d_ops_708 v0
  = coe MAlonzo.Code.Once.LinCore.Code.d_ops_858 (coe v0)
-- Once.LinCore.Layout._.Codeᴵ
d_Code'7477'_722 a0 a1 a2 a3 = ()
-- Once.LinCore.Layout._.Insᴵ
d_Ins'7477'_724 a0 a1 a2 a3 = ()
-- Once.LinCore.Layout.ws
d_ws_988 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] -> Integer
d_ws_988 ~v0 ~v1 v2 = du_ws_988 v2
du_ws_988 :: [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] -> Integer
du_ws_988 v0
  = case coe v0 of
      [] -> coe (0 :: Integer)
      (:) v1 v2
        -> coe
             addInt (coe du_ws_988 (coe v2))
             (coe MAlonzo.Code.Once.LinCore.Values.du_wsz_746 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Layout.envW
d_envW_994 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_850 -> Integer
d_envW_994 ~v0 ~v1 v2 = du_envW_994 v2
du_envW_994 :: MAlonzo.Code.Once.LinCore.Code.T_Sh_850 -> Integer
du_envW_994 v0
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Code.C__'8739'__860 v1 v2
        -> coe du_ws_988 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Layout.opW
d_opW_1000 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_850 -> Integer
d_opW_1000 ~v0 ~v1 v2 = du_opW_1000 v2
du_opW_1000 :: MAlonzo.Code.Once.LinCore.Code.T_Sh_850 -> Integer
du_opW_1000 v0
  = case coe v0 of
      MAlonzo.Code.Once.LinCore.Code.C__'8739'__860 v1 v2
        -> coe du_ws_988 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Layout._⊔²_
d__'8852''178'__1006 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'8852''178'__1006 ~v0 ~v1 v2 v3 = du__'8852''178'__1006 v2 v3
du__'8852''178'__1006 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du__'8852''178'__1006 v0 v1
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
d_at_1016 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_850 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_at_1016 ~v0 ~v1 v2 = du_at_1016 v2
du_at_1016 ::
  MAlonzo.Code.Once.LinCore.Code.T_Sh_850 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_at_1016 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_envW_994 (coe v0)) (coe du_opW_1000 (coe v0))
-- Once.LinCore.Layout.peakI
d_peakI_1024 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_850 ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_850 ->
  MAlonzo.Code.Once.LinCore.Image.T_Ins'7477'_1154 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_peakI_1024 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
              (coe (0 :: Integer)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Once.LinCore.Image.C_swap_1184
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Code.C__'8739'__860 v10 v11
                  -> case coe v11 of
                       (:) v12 v13
                         -> case coe v13 of
                              (:) v14 v15
                                -> case coe v3 of
                                     MAlonzo.Code.Once.LinCore.Code.C__'8739'__860 v16 v17
                                       -> case coe v17 of
                                            (:) v18 v19
                                              -> case coe v19 of
                                                   (:) v20 v21
                                                     -> coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe (0 :: Integer))
                                                          (coe
                                                             addInt (coe du_ws_988 (coe v11))
                                                             (coe
                                                                MAlonzo.Code.Once.LinCore.Values.du_wsz_746
                                                                (coe v12)))
                                                   _ -> coe v5
                                            _ -> coe v5
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> coe v5
                       _ -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.LinCore.Image.C_prim_1204 v6 v7 v12
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Code.C__'8739'__860 v13 v14
                  -> case coe v14 of
                       (:) v15 v16
                         -> case coe v3 of
                              MAlonzo.Code.Once.LinCore.Code.C__'8739'__860 v17 v18
                                -> case coe v18 of
                                     (:) v19 v20
                                       -> case coe v12 of
                                            MAlonzo.Code.Once.LinCore.Core.C_lswap_860
                                              -> case coe v15 of
                                                   MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v24 v25
                                                     -> case coe v19 of
                                                          MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v26 v27
                                                            -> coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe (0 :: Integer))
                                                                 (coe
                                                                    addInt (coe du_ws_988 (coe v14))
                                                                    (coe
                                                                       MAlonzo.Code.Once.LinCore.Values.du_wsz_746
                                                                       (coe v24)))
                                                          _ -> coe v5
                                                   _ -> coe v5
                                            MAlonzo.Code.Once.LinCore.Core.C_ldist_914
                                              -> case coe v15 of
                                                   MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v25 v26
                                                     -> case coe v26 of
                                                          MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v27 v28
                                                            -> case coe v19 of
                                                                 MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v29 v30
                                                                   -> case coe v29 of
                                                                        MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v31 v32
                                                                          -> case coe v30 of
                                                                               MAlonzo.Code.Once.LinCore.Core.C__'8855't__184 v33 v34
                                                                                 -> coe
                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                      (coe
                                                                                         (0 ::
                                                                                            Integer))
                                                                                      (coe
                                                                                         addInt
                                                                                         (coe
                                                                                            du_ws_988
                                                                                            (coe
                                                                                               v14))
                                                                                         (coe
                                                                                            MAlonzo.Code.Once.LinCore.Values.du_wsz_746
                                                                                            (coe
                                                                                               v25)))
                                                                               _ -> coe v5
                                                                        _ -> coe v5
                                                                 _ -> coe v5
                                                          _ -> coe v5
                                                   _ -> coe v5
                                            _ -> coe v5
                                     _ -> coe v5
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Once.LinCore.Image.C_loop_1508 v11
           -> case coe v2 of
                MAlonzo.Code.Once.LinCore.Code.C__'8739'__860 v12 v13
                  -> case coe v12 of
                       (:) v14 v15
                         -> case coe v13 of
                              (:) v16 v17
                                -> case coe v3 of
                                     MAlonzo.Code.Once.LinCore.Code.C__'8739'__860 v18 v19
                                       -> case coe v18 of
                                            (:) v20 v21
                                              -> case coe v19 of
                                                   (:) v22 v23
                                                     -> coe
                                                          du_peakC_1030 (coe v0) (coe v1) (coe v2)
                                                          (coe v11)
                                                   _ -> coe v5
                                            _ -> coe v5
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> coe v5
                       _ -> coe v5
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v5)
-- Once.LinCore.Layout.peakC
d_peakC_1030 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_850 ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_850 ->
  MAlonzo.Code.Once.LinCore.Image.T_Code'7477'_1152 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_peakC_1030 v0 v1 v2 ~v3 v4 = du_peakC_1030 v0 v1 v2 v4
du_peakC_1030 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_850 ->
  MAlonzo.Code.Once.LinCore.Image.T_Code'7477'_1152 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_peakC_1030 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.LinCore.Image.C_end_1518
        -> coe du_at_1016 (coe v2)
      MAlonzo.Code.Once.LinCore.Image.C__'10814'__1526 v5 v7 v8
        -> coe
             du__'8852''178'__1006 (coe du_at_1016 (coe v2))
             (coe
                du__'8852''178'__1006
                (coe d_peakI_1024 (coe v0) (coe v1) (coe v2) (coe v5) (coe v7))
                (coe du_peakC_1030 (coe v0) (coe v1) (coe v5) (coe v8)))
      MAlonzo.Code.Once.LinCore.Image.C_case_1538 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.LinCore.Code.C__'8739'__860 v11 v12
               -> case coe v12 of
                    (:) v13 v14
                      -> case coe v13 of
                           MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v15 v16
                             -> coe
                                  du__'8852''178'__1006 (coe du_at_1016 (coe v2))
                                  (coe
                                     du__'8852''178'__1006
                                     (coe
                                        du_peakC_1030 (coe v0) (coe v1)
                                        (coe
                                           MAlonzo.Code.Once.LinCore.Code.C__'8739'__860 (coe v11)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v15)
                                              (coe v14)))
                                        (coe v9))
                                     (coe
                                        du_peakC_1030 (coe v0) (coe v1)
                                        (coe
                                           MAlonzo.Code.Once.LinCore.Code.C__'8739'__860 (coe v11)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v16)
                                              (coe v14)))
                                        (coe v10)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Image.C_ecase_1550 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.LinCore.Code.C__'8739'__860 v11 v12
               -> case coe v11 of
                    (:) v13 v14
                      -> case coe v13 of
                           MAlonzo.Code.Once.LinCore.Core.C__'8853't__186 v15 v16
                             -> coe
                                  du__'8852''178'__1006 (coe du_at_1016 (coe v2))
                                  (coe
                                     du__'8852''178'__1006
                                     (coe
                                        du_peakC_1030 (coe v0) (coe v1)
                                        (coe
                                           MAlonzo.Code.Once.LinCore.Code.C__'8739'__860
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v15)
                                              (coe v11))
                                           (coe v12))
                                        (coe v9))
                                     (coe
                                        du_peakC_1030 (coe v0) (coe v1)
                                        (coe
                                           MAlonzo.Code.Once.LinCore.Code.C__'8739'__860
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v16)
                                              (coe v11))
                                           (coe v12))
                                        (coe v10)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.LinCore.Image.C_halted_1556
        -> coe du_at_1016 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Layout.Frame
d_Frame_1080 a0 a1 = ()
data T_Frame_1080 = C_frame_1090 Integer Integer
-- Once.LinCore.Layout.Frame.EP
d_EP_1086 :: T_Frame_1080 -> Integer
d_EP_1086 v0
  = case coe v0 of
      C_frame_1090 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Layout.Frame.OP
d_OP_1088 :: T_Frame_1080 -> Integer
d_OP_1088 v0
  = case coe v0 of
      C_frame_1090 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.LinCore.Layout.budget
d_budget_1092 :: T_Frame_1080 -> Integer
d_budget_1092 v0
  = coe addInt (coe d_OP_1088 (coe v0)) (coe d_EP_1086 (coe v0))
-- Once.LinCore.Layout.frameOf
d_frameOf_1100 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_850 ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_850 ->
  MAlonzo.Code.Once.LinCore.Image.T_Code'7477'_1152 -> T_Frame_1080
d_frameOf_1100 v0 v1 v2 ~v3 v4 = du_frameOf_1100 v0 v1 v2 v4
du_frameOf_1100 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  MAlonzo.Code.Once.LinCore.Code.T_Sh_850 ->
  MAlonzo.Code.Once.LinCore.Image.T_Code'7477'_1152 -> T_Frame_1080
du_frameOf_1100 v0 v1 v2 v3
  = coe
      C_frame_1090
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe du_peakC_1030 (coe v0) (coe v1) (coe v2) (coe v3)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe du_peakC_1030 (coe v0) (coe v1) (coe v2) (coe v3)))
-- Once.LinCore.Layout.envAt
d_envAt_1104 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] -> Integer
d_envAt_1104 ~v0 ~v1 v2 = du_envAt_1104 v2
du_envAt_1104 ::
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] -> Integer
du_envAt_1104 v0 = coe du_ws_988 (coe v0)
-- Once.LinCore.Layout.opAt
d_opAt_1108 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.LinCore.Flat.T_Base_46 -> Integer) ->
  T_Frame_1080 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] -> Integer
d_opAt_1108 ~v0 ~v1 v2 v3 = du_opAt_1108 v2 v3
du_opAt_1108 ::
  T_Frame_1080 ->
  [MAlonzo.Code.Once.LinCore.Core.T_LTy_178] -> Integer
du_opAt_1108 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
      (addInt (coe d_OP_1088 (coe v0)) (coe d_EP_1086 (coe v0)))
      (coe du_ws_988 (coe v1))
